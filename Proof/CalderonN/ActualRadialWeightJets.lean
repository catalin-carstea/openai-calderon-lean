module

public import Proof.CalderonN.ActualConormalRadialRow
public import Proof.CalderonN.NormalRadialWeightRemainder

import Proof.CalderonN.CompactSmoothExtension
import Proof.CalderonN.ZonalProjection
import Proof.CalderonN.UniformFirstDensityTaylor
import Mathlib.Tactic

/-! Local extension and first jets of the scalar Gauss-row coefficient
on the actual radius-rescaled unit ball. -/

public section

noncomputable section
open Set Filter Metric Matrix
open scoped ContDiff Topology Matrix.Norms.Elementwise
set_option maxHeartbeats 2200000
set_option maxSynthPendingDepth 23
set_option backward.isDefEq.respectTransparency false

namespace CalderonN

open BallDirichlet OAI.AnisotropicCalderon.SphereHarmonic

variable {dim : ℕ} [NeZero dim] [Nontrivial (Fin dim)]

omit [NeZero dim] [Nontrivial (Fin dim)] in
private theorem scalarQuadraticCoefficient_sub_scalar
    (A : X dim → Mat dim) (z : X dim) (c : ℝ) :
    scalarQuadraticCoefficient (fun x => A x-c • (1 : Mat dim)) z =
      scalarQuadraticCoefficient A z-c*(∑ i, z i^2) := by
  classical
  unfold scalarQuadraticCoefficient
  simp only [Matrix.sub_apply,Matrix.smul_apply,smul_eq_mul,mul_sub,sub_mul,Finset.sum_sub_distrib]
  congr 1
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  calc
    (∑ j, z i*(c*(1 : Mat dim) i j)*z j) = ∑ j, if i = j then c*(z i)^2 else 0 := by
      apply Finset.sum_congr rfl
      intro j _
      by_cases h : i = j
      · subst j
        simp only [Matrix.one_apply,ite_true,mul_one]
        ring
      · simp [Matrix.one_apply,h]
    _ = _ := by simp

/-- The actual radial conormal weight has affine coefficient given by the
normalized first density jet. Its quadratic error has controlled first jets
on the same unit ball used for the Sobolev estimates. -/
theorem uniform_actual_radial_weight_remainder (hn : 2 ≤ dim)
    {Y Ω : Set (X dim)} (hΩ : IsOpen Ω) {m : ℕ} (hm : 4 ≤ m)
    (K ρ c₀ : ℝ) (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ)
    (hK : 1 ≤ K) (hρ : 0 < ρ) :
    ∃ η C : ℝ, 0 < η ∧ 0 ≤ C ∧ ∀ floor ≥ 1, ∀ ε, 0 ≤ ε → ε ≤ η → ∀ d,
      Admissible Y Ω K ρ c₀ M Cj floor ε d → ∀ y ∈ Y,
      let r := d.radius y
      let ell := firstDensityCenterLinear d y
      ‖ell‖ ≤ C ∧
      ∃ R : SmoothData dim,
        EqOn (fun z => 1+r*ell z+R.1 z) (firstNormalRadialWeight d y r) (standardSphere dim) ∧
        ∀ z ∈ closedBall (0 : X dim) 1, |R.1 z| ≤ C*r^2 ∧ ‖fderiv ℝ R.1 z‖ ≤ C*r^2 := by
  obtain ⟨η,Q,hη,hQ,hT⟩ := uniform_normalized_coefficient_remainder_C2 (Y := Y) hn
    hΩ hm K ρ c₀ M Cj hK hρ 2 (by norm_num)
  obtain ⟨ηD,_,hηD,_,hD⟩ := uniform_first_density_taylor (Y := Y) hΩ (by omega : 2 ≤ m)
    K ρ c₀ M Cj hK hρ 2 (by norm_num)
  obtain ⟨ηN,hηN,hN⟩ := uniform_normal_control_on_disk (Y := Y) hΩ (by omega : 2 ≤ m)
    K ρ c₀ M Cj hK hρ 1 zero_le_one
  let P := K^(dim-2)*(K^(dim-2)*((dim-2 : ℕ):ℝ)*K^2*|M ⟨1,by omega⟩|)
  let C := P+3*(dim : ℝ)^2*Q
  have hK' : 0 < K := zero_lt_one.trans_le hK
  have hP : 0 ≤ P := by dsimp only [P]; positivity
  refine ⟨min η (min ηD ηN),C,lt_min hη (lt_min hηD hηN),by dsimp only [C]; positivity,?_⟩
  intro floor hf ε hε hs d hd y hy
  dsimp only
  let r := d.radius y
  let ell := firstDensityCenterLinear d y
  let D := normalizedFirstCoefficientRemainder d y
  have hr : 0 < r := (hd.2.2.2.2.1.2 y hy).1
  have hE : ‖ell‖ ≤ P := by
    have hℓ : ell = (firstMetricDensityFactor d.γ d.g₁ y)⁻¹ • firstDensityCenterDerivative d y := rfl
    have hc : |(firstMetricDensityFactor d.γ d.g₁ y)⁻¹| ≤ K^(dim-2) := by
      rw [abs_of_pos (inv_pos.mpr (firstMetricDensityFactor_pos _ _ _))]
      exact hd.1.firstMetricDensityFactor_inverse_le hK' (hd.2.1.center_mem hy)
    have hb := (hD floor hf ε hε (hs.trans ((min_le_right _ _).trans (min_le_left _ _))) d hd y hy).2.2.1
    rw [hℓ,norm_smul,Real.norm_eq_abs]
    exact mul_le_mul hc hb (norm_nonneg _) (by positivity)
  have hP_C : P ≤ C := le_add_of_nonneg_right (by positivity)
  refine ⟨hE.trans hP_C,?_⟩
  have hOn (z : X dim) (hz : z ∈ closedBall (0 : X dim) 2) :=
    hT floor hf ε hε (hs.trans (min_le_left _ _)) d hd y hy z hz
  have hDOn : ContDiffOn ℝ ∞ D (ball (0 : X dim) 2) :=
    fun z hz => (hOn z (ball_subset_closedBall hz)).1.contDiffWithinAt
  obtain ⟨A,hA,_,U,hU,hBU,_,hAD⟩ := exists_contDiff_extension_near_compact isOpen_ball
    (isCompact_closedBall (0 : X dim) 1) (closedBall_subset_ball (by norm_num)) hDOn
  let R : SmoothData dim := ⟨scalarQuadraticCoefficient A,contDiff_scalarQuadraticCoefficient hA⟩
  refine ⟨R,?_ ,?_⟩
  · intro z hz
    have hz' := sphere_subset_closedBall hz
    have hEq := hAD (hBU hz')
    have hW (j : Fin dim) :
        ∑ i, z i*firstNormalVelocityCoefficient d y (r • frameVector d.frame y z) i j =
          firstNormalRadialWeight d y r z*z j := by
      have hFrame := hd.1.2.2.2.2.2.2.2 y (hd.2.1.center_mem hy)
      have hw := frameVector_mem_disk d.γ d.frame y z 1 hFrame hz'
      have h' := (hN floor hf ε hε (hs.trans ((min_le_right _ _).trans (min_le_right _ _))) d hd y hy _ hw).1.1
      exact hd.actualNormalCoeff_radial_row hn hΩ hK' hy hr.ne' z h' j
    have hSq : ∑ i : Fin dim, z i ^ 2 = 1 := unitSphere_sum_sq ⟨z,hz⟩
    have hSub : R.1 z = scalarQuadraticCoefficient
        (fun w => firstNormalVelocityCoefficient d y (r • frameVector d.frame y w)) z -
        (1+r*ell z) := by
      change scalarQuadraticCoefficient A z = _
      have hFun : scalarQuadraticCoefficient A z = scalarQuadraticCoefficient D z := by
        simp only [scalarQuadraticCoefficient,hEq]
      rw [hFun]
      change scalarQuadraticCoefficient (fun w =>
        firstNormalVelocityCoefficient d y (r • frameVector d.frame y w) -
          (1+r*ell w) • (1 : Mat dim)) z = _
      rw [show scalarQuadraticCoefficient (fun w =>
        firstNormalVelocityCoefficient d y (r • frameVector d.frame y w) -
          (1+r*ell w) • (1 : Mat dim)) z =
          scalarQuadraticCoefficient (fun w => firstNormalVelocityCoefficient d y
            (r • frameVector d.frame y w)-(1+r*ell z) • (1 : Mat dim)) z from rfl,
        scalarQuadraticCoefficient_sub_scalar,hSq,mul_one]
    change 1+r*ell z+R.1 z = _
    rw [hSub,← add_sub_assoc,add_comm (1+r*ell z),add_sub_cancel_right]
    change (∑ i, ∑ j, z i*firstNormalVelocityCoefficient d y (r • frameVector d.frame y z) i j*z j) = _
    rw [Finset.sum_comm]
    simp_rw [← Finset.sum_mul,hW]
    simp only [mul_assoc,← Finset.mul_sum,← pow_two,hSq,mul_one,r]
  · intro z hz
    have hLoc : A =ᶠ[𝓝 z] D := by
      filter_upwards [hU.mem_nhds (hBU hz)] with w hw using hAD hw
    have h := hOn z (closedBall_subset_closedBall (by norm_num : (1 : ℝ) ≤ 2) hz)
    have hV : ‖A z‖ ≤ Q*r^2 := hLoc.eq_of_nhds.symm ▸ h.2.1
    have hJ : ‖fderiv ℝ A z‖ ≤ Q*r^2 := by
      rw [hLoc.fderiv_eq]
      exact h.2.2.1
    have hz1 := mem_closedBall_zero_iff.mp hz
    have hC : 3*(dim : ℝ)^2*Q ≤ C := le_add_of_nonneg_left hP
    refine ⟨(abs_scalarQuadraticCoefficient_le hz1 _ (by positivity) hV).trans ?_,
      (norm_fderiv_scalarQuadraticCoefficient_le hA hz1 _ (by positivity) hV hJ).trans ?_⟩
    · have he : (dim : ℝ)^2*Q ≤ 3*(dim : ℝ)^2*Q := by nlinarith [mul_nonneg (sq_nonneg (dim : ℝ)) hQ]
      exact (by simpa only [mul_assoc] using mul_le_mul_of_nonneg_right (he.trans hC) (sq_nonneg r))
    · exact (by simpa only [mul_assoc] using mul_le_mul_of_nonneg_right hC (sq_nonneg r))

end CalderonN
