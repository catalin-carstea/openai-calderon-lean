import Proof.ParallelFirstPotentialNormalizedGraphs
import Proof.ParallelNormAssemblyReservedCubicCorePair
import Proof.ParallelNormAssemblyReservedCubicAdjointBound
import Proof.ParallelNormAssemblyReservedFirstWordMass

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2800000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
open Set
open scoped ContDiff Topology InnerProductSpace
namespace ShrinkingSpheres.ParallelEnergy
open OAI.AnisotropicCalderon.SphereHarmonic

variable {Y : Set X} {d : Data} {CF CT CG CK : ℝ}

def firstPotentialNormalizedCubic (P : PhysicalPrincipalData Y d CF CT) {y : X}
    (W : PhysicalPotentialQuarticData P y CG CK) (a : PhysicalPotentialGeneratorIndex)
    (p : PhysicalPotentialGeneratorIndex → PhysicalPotentialGeneratorIndex → ℝ)
    (u : SphereSobolev (3/2:ℝ)) : SphereSobolev (-(1/2:ℝ)) :=
  ∑ c : PhysicalPotentialGeneratorIndex,normalizedCoordinateGeneratorCoefficients d y a c •
    cubicWordAdjointCommutatorValue P W c p u

/-- Linear combination of the genuine cubic identities, with the actual
coordinate normalizations retained before taking any norm. -/
theorem firstPotential_normalized_adjoint_quadratic_pair
    (P : PhysicalPrincipalData Y d CF CT) {y : X} (hy : y ∈ Y)
    (W : PhysicalPotentialQuarticData P y CG CK) (a : PhysicalPotentialGeneratorIndex)
    (p : PhysicalPotentialGeneratorIndex → PhysicalPotentialGeneratorIndex → ℝ)
    (u h : SphereSobolev (3/2:ℝ))
    (V v : PhysicalPotentialGeneratorIndex → SphereSobolev (3/2:ℝ))
    (hV : ∀ b,sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num) (V b)=P.potentialGeneratorHigh y b u)
    (hv : ∀ b,sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num) (v b)=W.adjointHigh b u) :
    ⟪sphereSobolevInclusionL (1/2:ℝ) 0 (by norm_num) (firstPotentialNormalizedAdjointHigh W a h),
      sphereSobolevInclusionL (1/2:ℝ) 0 (by norm_num) (quadraticWordAdjointCoreValue P W p v)⟫_ℝ=
    sphereSobolevDualPairing (1/2:ℝ) (normalizedPotentialGeneratorHigh P y a u)
        (quadraticWordForwardWeakValue P y p h)-
      sphereSobolevDualPairing (1/2:ℝ)
        (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num) h)
        (firstPotentialNormalizedCubic P W a p u) := by
  have hh (c : PhysicalPotentialGeneratorIndex) :=
    adjoint_generator_quadratic_core_pair P hy W c p u h V v hV hv
  simp only [firstPotentialNormalizedAdjointHigh,firstPotentialNormalizedCubic,
    normalized_generator_high_old_words,_root_.sum_apply,_root_.smul_apply,map_sum,map_smul,
    sum_inner,inner_sum,real_inner_smul_left,sphereSobolevDualPairing,real_inner_smul_right]
  rw [←Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro c _
  have hhc := congrArg (fun t : ℝ => normalizedCoordinateGeneratorCoefficients d y a c*t) (hh c)
  simpa only [sphereSobolevDualPairing,mul_sub] using hhc

lemma firstPotential_normalized_coefficient_mass
    {Ω : Set X} {m : ℕ} {K ρ c₀ floor ε : ℝ} {M : Fin (m+1) → ℝ} {Cj : Fin 9 → ℝ}
    (hd : Admissible Y Ω K ρ c₀ M Cj floor ε d) (hK : 1 ≤ K)
    {y : X} (hy : y ∈ Y) (a : PhysicalPotentialGeneratorIndex) :
    ∑ c : PhysicalPotentialGeneratorIndex,|normalizedCoordinateGeneratorCoefficients d y a c| *
      potentialGeneratorWeight (d.radius y) c ≤ 3*K := by
  have hr := (hd.2.2.2.2.1.2 y hy).1
  have hFrame := hd.1.2.2.2.2.2.2.2 y (hd.2.1.center_mem hy)
  have hC (a j : I) : |frameCoordinateLinear d.γ d.frame y j (axis a)| ≤ K := by
    rw [frameCoordinateLinear_apply]
    exact hd.1.1.frame_coordinate_abs_bound hK d.frame (hd.2.1.center_mem hy) hFrame a j
  rcases a with u | (a | a)
  · simpa only [normalizedCoordinateGeneratorCoefficients,potentialGeneratorWeight,Fintype.sum_sum_type,
      Fintype.sum_unique,abs_one,abs_zero,zero_mul,Finset.sum_const_zero,mul_one,add_zero] using
      (show (1:ℝ) ≤ 3*K by linarith)
  · simp only [normalizedCoordinateGeneratorCoefficients,potentialGeneratorWeight,Fintype.sum_sum_type,
      Fintype.sum_unique,abs_zero,zero_mul,mul_one,Finset.sum_const_zero,zero_add,add_zero]
    calc
      _ ≤ ∑ j : I,K := Finset.sum_le_sum (fun j _ => hC a j)
      _ = _ := by simp only [Fin.sum_univ_three];ring
  · simp only [normalizedCoordinateGeneratorCoefficients,potentialGeneratorWeight,Fintype.sum_sum_type,
      Fintype.sum_unique,abs_zero,zero_mul,Finset.sum_const_zero,zero_add]
    have hTerm (j : I) : |(d.radius y)⁻¹*frameCoordinateLinear d.γ d.frame y j (axis a)| *d.radius y=
        |frameCoordinateLinear d.γ d.frame y j (axis a)| := by
      rw [abs_mul,abs_inv,abs_of_pos hr]
      field_simp
    simp only [hTerm]
    calc
      _ ≤ ∑ j : I,K := Finset.sum_le_sum (fun j _ => hC a j)
      _ = _ := by simp only [Fin.sum_univ_three];ring

/-- The normalized angular cubic commutator loses one angular order.
The radius in the native word is cancelled by its exact normalization. -/
theorem firstPotential_normalized_cubic_norm_bound
    {Ω : Set X} {m : ℕ} {K ρ c₀ floor ε : ℝ} {M : Fin (m+1) → ℝ} {Cj : Fin 9 → ℝ}
    (P : PhysicalPrincipalData Y d CF CT)
    (hd : Admissible Y Ω K ρ c₀ M Cj floor ε d) (hK : 1 ≤ K)
    {y : X} (hy : y ∈ Y) (hCG : 0 ≤ CG) (hCK : 0 ≤ CK)
    (W : PhysicalPotentialQuarticData P y CG CK) (a : PhysicalPotentialGeneratorIndex)
    (p : PhysicalPotentialGeneratorIndex → PhysicalPotentialGeneratorIndex → ℝ)
    (u : SphereSobolev (3/2:ℝ)) :
    let G := max (physicalPotentialGeneratorBudget CF) CG
    ‖firstPotentialNormalizedCubic P W a p u‖ ≤
      (6*K*G*CK)*quadraticWordCoefficientMass p (potentialGeneratorWeight (d.radius y))*‖u‖ := by
  let G := max (physicalPotentialGeneratorBudget CF) CG
  let w := potentialGeneratorWeight (d.radius y)
  let mass := quadraticWordCoefficientMass p w
  have hG : 0 ≤ G := hCG.trans (le_max_right _ _)
  have hr := (hd.2.2.2.2.1.2 y hy).1.le
  have hw := potentialGeneratorWeight_nonneg hr
  have hm : 0 ≤ mass := Finset.sum_nonneg (fun c _ => Finset.sum_nonneg (fun e _ =>
    mul_nonneg (mul_nonneg (abs_nonneg _) (hw c)) (hw e)))
  have hNorm (c : PhysicalPotentialGeneratorIndex) := cubic_word_adjoint_commutator_norm_bound P hy hr hCG hCK W c p u
  have hMass := firstPotential_normalized_coefficient_mass hd hK hy a
  calc
    _ ≤ ∑ c : PhysicalPotentialGeneratorIndex,
        ‖normalizedCoordinateGeneratorCoefficients d y a c • cubicWordAdjointCommutatorValue P W c p u‖ := norm_sum_le _ _
    _ ≤ ∑ c : PhysicalPotentialGeneratorIndex,
        |normalizedCoordinateGeneratorCoefficients d y a c| *((2*G*CK*w c)*mass*‖u‖) := by
      apply Finset.sum_le_sum
      intro c _
      rw [norm_smul,Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_left (hNorm c) (abs_nonneg _)
    _ = (∑ c : PhysicalPotentialGeneratorIndex,|normalizedCoordinateGeneratorCoefficients d y a c| *w c)*
        ((2*G*CK)*mass*‖u‖) := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro c _
      ring
    _ ≤ (3*K)*((2*G*CK)*mass*‖u‖) := mul_le_mul_of_nonneg_right hMass (by positivity)
    _ = _ := by ring

end ShrinkingSpheres.ParallelEnergy
