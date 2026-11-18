import Proof.LogJetBounds
import Proof.SecondDerivativeCompositionBounds

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Filter
open scoped ContDiff Topology
namespace ShrinkingSpheres

lemma norm_fderiv_scalar_inverse_le {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    (f : P → ℝ) (x : P) (hf : DifferentiableAt ℝ f x) (hpos : 0 < f x)
    (M : ℝ) (hD : ‖fderiv ℝ f x‖ ≤ M) :
    ‖fderiv ℝ (fun y => (f y)⁻¹) x‖ ≤ (f x)⁻¹^2*M := by
  have hInv := (hasDerivAt_inv hpos.ne').comp_hasFDerivAt x hf.hasFDerivAt
  simp only [Function.comp_def] at hInv
  rw [hInv.fderiv,norm_smul,Real.norm_eq_abs,abs_neg,← inv_pow,
    abs_of_nonneg (sq_nonneg (f x)⁻¹)]
  exact mul_le_mul_of_nonneg_left hD (sq_nonneg _)

/-- The actual scalar inverse has a second jet controlled only by the inverse
    value and the first two jets of its positive denominator. -/
theorem norm_second_fderiv_scalar_inverse_le {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    (f : P → ℝ) (x : P) (hf : ContDiffAt ℝ ∞ f x) (hpos : 0 < f x)
    (M1 M2 : ℝ) (hM1 : 0 ≤ M1) (_hM2 : 0 ≤ M2)
    (hD : ‖fderiv ℝ f x‖ ≤ M1) (hDD : ‖fderiv ℝ (fderiv ℝ f) x‖ ≤ M2) :
    ‖fderiv ℝ (fderiv ℝ (fun y => (f y)⁻¹)) x‖ ≤
      (f x)⁻¹^2*M2+2*(f x)⁻¹^3*M1^2 := by
  have hFD := (hf.differentiableAt (by simp)).hasFDerivAt
  have hDDF := ((hf.fderiv_right (m:=∞) (by simp)).differentiableAt (by simp)).hasFDerivAt
  have hInv := (hasDerivAt_inv hpos.ne').comp_hasFDerivAt x hFD
  simp only [Function.comp_def] at hInv
  have hInvBound := norm_fderiv_scalar_inverse_le f x (hf.differentiableAt (by simp)) hpos M1 hD
  have hA := (hInv.pow 2).neg
  change HasFDerivAt (fun y => -((f y)⁻¹)^2) _ x at hA
  have hABound : ‖fderiv ℝ (fun y => -((f y)⁻¹)^2) x‖ ≤ 2*(f x)⁻¹^3*M1 := by
    rw [hA.fderiv,norm_neg,norm_smul,Real.norm_eq_abs]
    simp only [Nat.reduceSub,pow_one,nsmul_eq_mul,abs_mul,
      abs_of_pos (inv_pos.mpr hpos)]
    have hB := hInvBound
    rw [hInv.fderiv] at hB
    exact (mul_le_mul_of_nonneg_left hB (by positivity)).trans_eq (by ring)
  have hNear := (hf.of_le (show (1:ℕ∞ω) ≤ ∞ by simp)).eventually (by simp)
  have hPositive := hf.continuousAt.eventually (isOpen_Ioi.mem_nhds hpos)
  have hEq : fderiv ℝ (fun y => (f y)⁻¹) =ᶠ[𝓝 x]
      (fun y => -((f y)⁻¹)^2 • fderiv ℝ f y) := by
    filter_upwards [hNear,hPositive] with y hy hp
    have hh := ((hasDerivAt_inv hp.ne').comp_hasFDerivAt y (hy.differentiableAt (by simp)).hasFDerivAt).fderiv
    simpa only [Function.comp_def,inv_pow] using hh
  have hProd := hA.smul hDDF
  change HasFDerivAt (fun y => -((f y)⁻¹)^2 • fderiv ℝ f y) _ x at hProd
  rw [hEq.fderiv_eq,hProd.fderiv]
  calc
    _ ≤ ‖-((f x)⁻¹)^2 • fderiv ℝ (fderiv ℝ f) x‖+
      ‖(fderiv ℝ (fun y => -((f y)⁻¹)^2) x).smulRight (fderiv ℝ f x)‖ := by
        rw [hA.fderiv];exact norm_add_le _ _
    _ = (f x)⁻¹^2*‖fderiv ℝ (fderiv ℝ f) x‖+
      ‖fderiv ℝ (fun y => -((f y)⁻¹)^2) x‖*‖fderiv ℝ f x‖ := by
        rw [ContinuousLinearMap.norm_smulRight_apply,norm_smul,Real.norm_eq_abs,abs_neg,abs_of_nonneg (sq_nonneg _)]
    _ ≤ (f x)⁻¹^2*M2+(2*(f x)⁻¹^3*M1)*M1 := by gcongr
    _ = _ := by ring

end ShrinkingSpheres
