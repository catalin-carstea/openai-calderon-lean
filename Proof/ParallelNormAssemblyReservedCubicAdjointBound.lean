import Proof.ParallelNormAssemblyReservedCubicAdjoint
import Proof.CoarseProductFirstDensity

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2800000
set_option maxRecDepth 10000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set
open scoped ContDiff Topology InnerProductSpace
namespace ShrinkingSpheres.ParallelEnergy
open OAI.AnisotropicCalderon.SphereHarmonic

theorem cubic_word_adjoint_commutator_norm_bound {Y : Set X} {d : Data} {CF CT CG CK : ℝ}
    (P : PhysicalPrincipalData Y d CF CT) {y : X} (hy : y ∈ Y)
    (hr : 0 ≤ d.radius y) (hCG : 0 ≤ CG) (hCK : 0 ≤ CK)
    (W : PhysicalPotentialQuarticData P y CG CK)
    (a : PhysicalPotentialGeneratorIndex)
    (p : PhysicalPotentialGeneratorIndex → PhysicalPotentialGeneratorIndex → ℝ)
    (u : SphereSobolev (3/2:ℝ)) :
    let G := max (physicalPotentialGeneratorBudget CF) CG
    ‖cubicWordAdjointCommutatorValue P W a p u‖ ≤
      (2*G*CK*potentialGeneratorWeight (d.radius y) a)*
        quadraticWordCoefficientMass p (potentialGeneratorWeight (d.radius y))*‖u‖ := by
  let G := max (physicalPotentialGeneratorBudget CF) CG
  let w := potentialGeneratorWeight (d.radius y)
  have hG : 0 ≤ G := hCG.trans (le_max_right _ _)
  have hw := potentialGeneratorWeight_nonneg hr
  have hL (c : PhysicalPotentialGeneratorIndex) : ‖(P.potentialGeneratorLow y c).adjoint‖ ≤ G*w c := by
    rw [ContinuousLinearMap.adjoint.norm_map]
    exact ((P.potential_generator_norm_bounds hy hr c).1).trans
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (hw c))
  have hA (e : PhysicalPotentialGeneratorIndex) : ‖W.adjointHigh e‖ ≤ G*w e :=
    (W.adjoint_bound e).trans (mul_le_mul_of_nonneg_right (le_max_right _ _) (hw e))
  have hTerm (c e : PhysicalPotentialGeneratorIndex) :
      ‖(P.potentialGeneratorLow y e).adjoint (W.commHigh c a u)+W.commLow e a (W.adjointHigh c u)‖ ≤
        (2*G*CK*w a)*(w c*w e)*‖u‖ := by
    have h1 : ‖(P.potentialGeneratorLow y e).adjoint (W.commHigh c a u)‖ ≤
        (G*w e)*(CK*w c*w a*‖u‖) := by
      exact (((P.potentialGeneratorLow y e).adjoint).le_opNorm _).trans
        (mul_le_mul (hL e) (((W.commHigh c a).le_opNorm u).trans
          (mul_le_mul_of_nonneg_right (W.commHigh_bound c a) (norm_nonneg u)))
          (norm_nonneg _) (mul_nonneg hG (hw e)))
    have h2 : ‖W.commLow e a (W.adjointHigh c u)‖ ≤
        (CK*w e*w a)*(G*w c*‖u‖) := by
      exact ((W.commLow e a).le_opNorm _).trans
        (mul_le_mul (W.commLow_bound e a) (((W.adjointHigh c).le_opNorm u).trans
          (mul_le_mul_of_nonneg_right (hA c) (norm_nonneg u)))
          (norm_nonneg _) (mul_nonneg (mul_nonneg hCK (hw e)) (hw a)))
    exact ((norm_add_le _ _).trans (add_le_add h1 h2)).trans_eq (by ring)
  calc
    _ ≤ ∑ c : PhysicalPotentialGeneratorIndex,∑ e : PhysicalPotentialGeneratorIndex,
        ‖p c e • ((P.potentialGeneratorLow y e).adjoint (W.commHigh c a u)+W.commLow e a (W.adjointHigh c u))‖ :=
      (norm_sum_le _ _).trans (Finset.sum_le_sum (fun c _ => norm_sum_le _ _))
    _ ≤ ∑ c : PhysicalPotentialGeneratorIndex,∑ e : PhysicalPotentialGeneratorIndex,
        |p c e| *((2*G*CK*w a)*(w c*w e)*‖u‖) := by
      apply Finset.sum_le_sum
      intro c _
      apply Finset.sum_le_sum
      intro e _
      rw [norm_smul,Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_left (hTerm c e) (abs_nonneg _)
    _ = (2*G*CK*w a)*quadraticWordCoefficientMass p w*‖u‖ := by
      simp only [quadraticWordCoefficientMass,Finset.mul_sum,Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro c _
      apply Finset.sum_congr rfl
      intro e _
      ring

/-- In the transposed model/potential cubic term the actual horizontal
source requires ONLY its H1/2 norm. This is the needed energy orientation,
with the same complete potential and the same W. -/
theorem actual_potential_cubic_transposed_pair_point_bound {Y Ω : Set X} {m : ℕ}
    {K ρ c₀ floor ε CF CT CG CK : ℝ} {M : Fin (m+1) → ℝ} {Cj : Fin 9 → ℝ} {d : Data}
    (P : PhysicalPrincipalData Y d CF CT)
    (hd : Admissible Y Ω K ρ c₀ M Cj floor ε d) (hK : 1 ≤ K) (hf : 1 ≤ floor)
    (hε : 0 ≤ ε) (hε1 : ε ≤ 1) {y : X} (hy : y ∈ Y)
    (hCG : 0 ≤ CG) (hCK : 0 ≤ CK) (W : PhysicalPotentialQuarticData P y CG CK)
    (i : I) (u v : SphereSobolev (3/2:ℝ)) :
    let G := max (physicalPotentialGeneratorBudget CF) CG
    let CW := 49*potentialWordEntryBudget K
    |sphereSobolevDualPairing (1/2:ℝ)
      (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num) v)
      (cubicWordCommutatorValue P W (.inr (.inl i)) (PhysicalPrincipalData.potentialWordCoefficient d y) u)| ≤
      (2*G*CK*CW)*ε*((beta d.γ d.radius y)⁻¹*
        ‖sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num) u‖^2+beta d.γ d.radius y*‖v‖^2) := by
  let G := max (physicalPotentialGeneratorBudget CF) CG
  let CW := 49*potentialWordEntryBudget K
  let β := beta d.γ d.radius y
  let Ju := sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num) u
  have hG : 0 ≤ G := hCG.trans (le_max_right _ _)
  have hCW : 0 ≤ CW := by
    have hK0 := zero_le_one.trans hK
    dsimp only [CW,potentialWordEntryBudget]
    positivity
  have hr := (hd.2.2.2.2.1.2 y hy).1.le
  have hβ : 0 < β := zero_lt_one.trans_le (hf.trans (hd.2.2.2.2.1.2 y hy).2.1)
  rw [cubic_word_commutator_dual_adjoint P hy W]
  have hN := cubic_word_adjoint_commutator_norm_bound P hy hr hCG hCK W (.inr (.inl i))
    (PhysicalPrincipalData.potentialWordCoefficient d y) v
  simp only [potentialGeneratorWeight,mul_one] at hN
  have hMass : quadraticWordCoefficientMass (PhysicalPrincipalData.potentialWordCoefficient d y)
      (potentialGeneratorWeight (d.radius y)) ≤ CW*ε := hd.potentialWordMass_le hK hf hε hε1 hy
  have hNN : ‖cubicWordAdjointCommutatorValue P W (.inr (.inl i)) (PhysicalPrincipalData.potentialWordCoefficient d y) v‖ ≤
      (2*G*CK*CW)*ε*‖v‖ := by
    exact hN.trans ((mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hMass
      (show 0 ≤ 2*G*CK by positivity)) (norm_nonneg v)).trans_eq (by ring))
  calc
    _ ≤ ‖Ju‖*‖cubicWordAdjointCommutatorValue P W (.inr (.inl i)) (PhysicalPrincipalData.potentialWordCoefficient d y) v‖ :=
      abs_sphereSobolevDualPairing_le _ _ _
    _ ≤ ‖Ju‖*((2*G*CK*CW)*ε*‖v‖) := mul_le_mul_of_nonneg_left hNN (norm_nonneg Ju)
    _ = ((2*G*CK*CW)*ε)*(‖Ju‖*‖v‖) := by ring
    _ ≤ ((2*G*CK*CW)*ε)*(β⁻¹*‖Ju‖^2+β*‖v‖^2) :=
      mul_le_mul_of_nonneg_left (weighted_product_le ‖Ju‖ ‖v‖ β hβ) (by positivity)

end ShrinkingSpheres.ParallelEnergy
