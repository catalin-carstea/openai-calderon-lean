import Proof.ParallelModelFirstZeroCubic
import Proof.ParallelNormAssemblyReservedFirstWordMass

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2800000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
open Set
open scoped InnerProductSpace
namespace ShrinkingSpheres.ParallelEnergy
open OAI.AnisotropicCalderon.SphereHarmonic

lemma model_first_normalized_generator_coefficient_mass
    {Y Ω : Set X} {m : ℕ} {K ρ c₀ floor ε : ℝ} {M : Fin (m+1) → ℝ} {Cj : Fin 9 → ℝ} {d : Data}
    (hd : Admissible Y Ω K ρ c₀ M Cj floor ε d) (hK : 1 ≤ K) {y : X} (hy : y ∈ Y)
    (a : PhysicalPotentialGeneratorIndex) :
    (∑ e : PhysicalPotentialGeneratorIndex,|normalizedCoordinateGeneratorCoefficients d y a e| *potentialGeneratorWeight (d.radius y) e) ≤ 3*K+1 := by
  have hr := (hd.2.2.2.2.1.2 y hy).1
  have hFrame := hd.1.2.2.2.2.2.2.2 y (hd.2.1.center_mem hy)
  have hCF (c i : I) : |frameCoordinateLinear d.γ d.frame y i (axis c)| ≤ K := by
    rw [frameCoordinateLinear_apply]
    exact hd.1.1.frame_coordinate_abs_bound hK d.frame (hd.2.1.center_mem hy) hFrame c i
  have hSum (c : I) : (∑ i : I,|frameCoordinateLinear d.γ d.frame y i (axis c)|) ≤ 3*K+1 := by
    have hh : (∑ i : I,|frameCoordinateLinear d.γ d.frame y i (axis c)|) ≤ 3*K := by
      calc
        _ ≤ ∑ _i : I,K := Finset.sum_le_sum (fun i _ => hCF c i)
        _ = 3*K := by simp only [Fin.sum_univ_three];ring
    exact hh.trans (by linarith)
  have hCancel (c i : I) : |(d.radius y)⁻¹*frameCoordinateLinear d.γ d.frame y i (axis c)| *d.radius y=
      |frameCoordinateLinear d.γ d.frame y i (axis c)| := by
    rw [abs_mul,abs_inv,abs_of_pos hr]
    field_simp [hr.ne'] <;> ring
  rcases a with u | (c | c)
  · simp only [normalizedCoordinateGeneratorCoefficients,Fintype.sum_sum_type,Fintype.sum_unique,potentialGeneratorWeight,
      abs_zero,abs_one,mul_one,zero_mul,Finset.sum_const_zero,add_zero]
    linarith only [hK]
  · simpa only [normalizedCoordinateGeneratorCoefficients,Fintype.sum_sum_type,Fintype.sum_unique,potentialGeneratorWeight,
      abs_zero,mul_one,zero_mul,Finset.sum_const_zero,add_zero,zero_add] using hSum c
  · simpa only [normalizedCoordinateGeneratorCoefficients,Fintype.sum_sum_type,Fintype.sum_unique,potentialGeneratorWeight,
      abs_zero,mul_one,zero_mul,Finset.sum_const_zero,add_zero,zero_add,hCancel] using hSum c

/-- Normalization cancels the native error's radius weight exactly, so
one commutator with R_c D has a fixed background order-two norm budget. -/
theorem model_first_normalized_zero_commutator_norm_bound
    {Y Ω : Set X} {m : ℕ} {K ρ c₀ floor ε CF CT CG CK : ℝ}
    {M : Fin (m+1) → ℝ} {Cj : Fin 9 → ℝ} {d : Data}
    (hd : Admissible Y Ω K ρ c₀ M Cj floor ε d) (hK : 1 ≤ K)
    (P : PhysicalPrincipalData Y d CF CT) {y : X} (hy : y ∈ Y)
    (W : PhysicalPotentialQuarticData P y CG CK) (hCG : 0 ≤ CG) (hCK : 0 ≤ CK)
    (c : I) (a : PhysicalPotentialGeneratorIndex) (u : SphereSobolev (3/2:ℝ)) :
    ‖modelFirstNormalizedZeroCommutatorValue P W c a u‖ ≤
      (6*K*max (physicalPotentialGeneratorBudget CF) CG*CK*(3*K+1))*‖u‖ := by
  let G := max (physicalPotentialGeneratorBudget CF) CG
  let C := 6*K*G*CK
  have hG : 0 ≤ G := hCG.trans (le_max_right _ _)
  have hC : 0 ≤ C := by dsimp only [C];positivity
  have hr := (hd.2.2.2.2.1.2 y hy).1.le
  have hw := potentialGeneratorWeight_nonneg hr
  have hRaw (e : PhysicalPotentialGeneratorIndex) :
      ‖cubicWordCommutatorValue P W e (modelFirstZeroWordCoefficient d c y) u‖ ≤ C*potentialGeneratorWeight (d.radius y) e*‖u‖ := by
    have hMass := model_first_zero_word_mass_bound hd hK hy c
    have hN := cubic_word_commutator_norm_bound P hy hr hCG hCK W e (modelFirstZeroWordCoefficient d c y) u
    have hFactor : 0 ≤ 2*G*CK*potentialGeneratorWeight (d.radius y) e :=
      mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hG) hCK) (hw e)
    exact hN.trans ((mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hMass
      hFactor) (norm_nonneg _)).trans_eq (by dsimp only [C];ring))
  unfold modelFirstNormalizedZeroCommutatorValue
  calc
    _ ≤ ∑ e : PhysicalPotentialGeneratorIndex,‖normalizedCoordinateGeneratorCoefficients d y a e •
        cubicWordCommutatorValue P W e (modelFirstZeroWordCoefficient d c y) u‖ := norm_sum_le _ _
    _ ≤ ∑ e : PhysicalPotentialGeneratorIndex,|normalizedCoordinateGeneratorCoefficients d y a e| *(C*potentialGeneratorWeight (d.radius y) e*‖u‖) :=
      Finset.sum_le_sum (fun e _ => by rw [norm_smul,Real.norm_eq_abs];exact mul_le_mul_of_nonneg_left (hRaw e) (abs_nonneg _))
    _ = (C*‖u‖)*(∑ e : PhysicalPotentialGeneratorIndex,|normalizedCoordinateGeneratorCoefficients d y a e| *potentialGeneratorWeight (d.radius y) e) := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl (fun e _ => by ring)
    _ ≤ (C*‖u‖)*(3*K+1) := mul_le_mul_of_nonneg_left (model_first_normalized_generator_coefficient_mass hd hK hy a) (mul_nonneg hC (norm_nonneg _))
    _ = _ := by dsimp only [C,G];ring

def modelFirstZeroWordResidualValue {Y : Set X} {d : Data} {CF CT CG CK : ℝ}
    (P : PhysicalPrincipalData Y d CF CT) {y : X} (W : PhysicalPotentialQuarticData P y CG CK)
    (b c : I) (u : SphereSobolev (3/2:ℝ)) : SphereSobolev (-(1/2:ℝ)) :=
  ∑ a : PhysicalPotentialGeneratorIndex,effectiveFirstWordCoefficient d b y a •
    modelFirstNormalizedZeroCommutatorValue P W c a u

/-- The COMPLETE angular part of B has its original epsilon/beta
coefficient mass before the paired zero-model density is estimated. -/
theorem model_first_zero_word_residual_norm_bound
    {Y Ω : Set X} {m : ℕ} {K ρ c₀ floor ε CF CT CG CK CW : ℝ}
    {M : Fin (m+1) → ℝ} {Cj : Fin 9 → ℝ} {d : Data}
    (hd : Admissible Y Ω K ρ c₀ M Cj floor ε d) (hK : 1 ≤ K)
    (P : PhysicalPrincipalData Y d CF CT) {y : X} (hy : y ∈ Y)
    (W : PhysicalPotentialQuarticData P y CG CK) (hCG : 0 ≤ CG) (hCK : 0 ≤ CK)
    (hCW : 0 ≤ CW) (b c : I) (u : SphereSobolev (3/2:ℝ))
    (hMass : (∑ a : PhysicalPotentialGeneratorIndex,|effectiveFirstWordCoefficient d b y a|) ≤ CW*ε/beta d.γ d.radius y) :
    ‖modelFirstZeroWordResidualValue P W b c u‖ ≤
      (6*K*max (physicalPotentialGeneratorBudget CF) CG*CK*(3*K+1)*CW)*ε/beta d.γ d.radius y*‖u‖ := by
  let C := 6*K*max (physicalPotentialGeneratorBudget CF) CG*CK*(3*K+1)
  have hG : 0 ≤ max (physicalPotentialGeneratorBudget CF) CG := hCG.trans (le_max_right _ _)
  have hC : 0 ≤ C := by dsimp only [C];positivity
  unfold modelFirstZeroWordResidualValue
  calc
    _ ≤ ∑ a : PhysicalPotentialGeneratorIndex,‖effectiveFirstWordCoefficient d b y a • modelFirstNormalizedZeroCommutatorValue P W c a u‖ := norm_sum_le _ _
    _ ≤ ∑ a : PhysicalPotentialGeneratorIndex,|effectiveFirstWordCoefficient d b y a| *(C*‖u‖) :=
      by
        apply Finset.sum_le_sum
        intro a _
        rw [norm_smul,Real.norm_eq_abs]
        exact mul_le_mul_of_nonneg_left
          (model_first_normalized_zero_commutator_norm_bound hd hK P hy W hCG hCK c a u) (abs_nonneg _)
    _ = (C*‖u‖)*(∑ a : PhysicalPotentialGeneratorIndex,|effectiveFirstWordCoefficient d b y a|) := by
      rw [Finset.mul_sum];exact Finset.sum_congr rfl (fun a _ => by ring)
    _ ≤ (C*‖u‖)*(CW*ε/beta d.γ d.radius y) := mul_le_mul_of_nonneg_left hMass (mul_nonneg hC (norm_nonneg _))
    _ = _ := by dsimp only [C];ring

end ShrinkingSpheres.ParallelEnergy
