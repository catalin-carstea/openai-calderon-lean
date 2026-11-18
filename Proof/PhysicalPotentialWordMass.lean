import Proof.FiniteQuadraticWordNormBound
import Proof.PhysicalPotentialWordCoefficientBounds
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option maxSynthPendingDepth 30
open Set
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.SphereHarmonic

lemma potentialWordMass_nonneg (d : Data) (y : X) (hr : 0 ≤ d.radius y) : 0 ≤ potentialWordMass d y := by
  exact Finset.sum_nonneg (fun a _ => Finset.sum_nonneg (fun b _ =>
    mul_nonneg (mul_nonneg (abs_nonneg _) (potentialGeneratorWeight_nonneg hr a))
      (potentialGeneratorWeight_nonneg hr b)))

theorem Admissible.potentialWordMass_le {Y Ω : Set X}
    {m : ℕ} {K ρ c₀ floor ε : ℝ} {M : Fin (m+1) → ℝ} {Cj : Fin 9 → ℝ} {d : Data}
    (hd : Admissible Y Ω K ρ c₀ M Cj floor ε d) (hK : 1 ≤ K) (hf : 1 ≤ floor)
    (hε : 0 ≤ ε) (hε1 : ε ≤ 1) {y : X} (hy : y ∈ Y) :
    potentialWordMass d y ≤ (49*potentialWordEntryBudget K)*ε := by
  calc
    _ ≤ ∑ _a : PhysicalPotentialGeneratorIndex,∑ _b : PhysicalPotentialGeneratorIndex,potentialWordEntryBudget K*ε :=
      Finset.sum_le_sum (fun a _ => Finset.sum_le_sum (fun b _ => hd.potentialWordWeightedEntry_le hK hf hε hε1 hy a b))
    _ = _ := by simp only [Fintype.sum_sum_type,Fintype.sum_unique,Fin.sum_univ_three];ring

/-- Finite genuine quadratic words are controlled by their weighted
    coefficient mass. No operators on different grades are identified. -/
lemma norm_finite_quadratic_words_le_mass {ι : Type*} [Fintype ι]
    (c : ι → ι → ℝ)
    (Lo : ι → SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ)))
    (Hi : ι → SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ))
    (w : ι → ℝ) {B : ℝ} (hB : 0 ≤ B) (hw : ∀ a,0 ≤ w a)
    (hL : ∀ a,‖Lo a‖ ≤ B*w a) (hH : ∀ a,‖Hi a‖ ≤ B*w a) :
    ‖∑ a,∑ b,c a b • (Lo a).comp (Hi b)‖ ≤ B^2*(∑ a,∑ b,|c a b| *w a*w b) := by
  simpa only [pow_two] using norm_finite_mixed_quadratic_words_le_mass c Lo Hi w hB hB hw hL hH

namespace PhysicalPrincipalData
variable {Y : Set X} {d : Data} {CF CT : ℝ}

lemma norm_potentialQuadraticHalfL_le_word_mass (P : PhysicalPrincipalData Y d CF CT)
    {y : X} (hy : y ∈ Y) (hr : 0 ≤ d.radius y) :
    ‖P.potentialQuadraticHalfL y‖ ≤ (physicalPotentialGeneratorBudget CF)^2*potentialWordMass d y := by
  rw [P.potentialQuadraticHalfL_eq_word_matrix]
  exact norm_finite_quadratic_words_le_mass _ _ _ _
    ((by norm_num : (0:ℝ) ≤ 2).trans (physicalPotentialGeneratorBudget_bounds CF).1)
    (potentialGeneratorWeight_nonneg hr) (fun a => (P.potential_generator_norm_bounds hy hr a).1)
    (fun a => (P.potential_generator_norm_bounds hy hr a).2)

lemma norm_potentialQuadraticHalfL_weighted_small {Ω : Set X}
    {m : ℕ} {K ρ c₀ floor ε : ℝ} {M : Fin (m+1) → ℝ} {Cj : Fin 9 → ℝ}
    (P : PhysicalPrincipalData Y d CF CT)
    (hd : Admissible Y Ω K ρ c₀ M Cj floor ε d) (hK : 1 ≤ K) (hf : 1 ≤ floor)
    (hε : 0 ≤ ε) (hε1 : ε ≤ 1) {y : X} (hy : y ∈ Y) :
    ‖P.potentialQuadraticHalfL y‖ ≤ ((physicalPotentialGeneratorBudget CF)^2*(49*potentialWordEntryBudget K))*ε :=
  (P.norm_potentialQuadraticHalfL_le_word_mass hy (hd.2.2.2.2.1.2 y hy).1.le).trans
    ((mul_le_mul_of_nonneg_left (hd.potentialWordMass_le hK hf hε hε1 hy) (sq_nonneg _)).trans_eq (by ring))
end PhysicalPrincipalData
end ShrinkingSpheres
