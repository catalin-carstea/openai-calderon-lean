import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Tactic

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxSynthPendingDepth 15
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Filter
open scoped ContDiff Topology
namespace ShrinkingSpheres

lemma norm_fderiv_log_le {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (f : V → ℝ) (x : V) (hf : DifferentiableAt ℝ f x) (hpos : 0 < f x)
    (M : ℝ) (hM : ‖fderiv ℝ f x‖ ≤ M) :
    ‖fderiv ℝ (fun y => Real.log (f y)) x‖ ≤ (f x)⁻¹*M := by
  rw [(hf.hasFDerivAt.log hpos.ne').fderiv,norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hpos)]
  exact mul_le_mul_of_nonneg_left hM (inv_nonneg.mpr hpos.le)

/-- An explicit second logarithmic jet bound, used for the actual conformal
    depth. It only uses the first two scalar jets at this point. -/
theorem norm_second_fderiv_log_le {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (f : V → ℝ) (x : V) (hf : ContDiffAt ℝ ∞ f x) (hpos : 0 < f x)
    (M1 M2 : ℝ) (hM1 : 0 ≤ M1) (hM2 : 0 ≤ M2)
    (hD : ‖fderiv ℝ f x‖ ≤ M1) (hDD : ‖fderiv ℝ (fderiv ℝ f) x‖ ≤ M2) :
    ‖fderiv ℝ (fderiv ℝ (fun y => Real.log (f y))) x‖ ≤
      (f x)⁻¹*M2+((f x)^2)⁻¹*M1^2 := by
  have hNear := (hf.of_le (show (1:ℕ∞ω) ≤ ∞ by simp)).eventually (by simp)
  have hPositive : ∀ᶠ y in 𝓝 x,0 < f y := hf.continuousAt.eventually (isOpen_Ioi.mem_nhds hpos)
  have hEq : fderiv ℝ (fun y => Real.log (f y)) =ᶠ[𝓝 x] (fun y => (f y)⁻¹ • fderiv ℝ f y) := by
    filter_upwards [hNear,hPositive] with y hy hp
    exact ((hy.differentiableAt (by simp)).hasFDerivAt.log hp.ne').fderiv
  have hFD := (hf.differentiableAt (by simp)).hasFDerivAt
  have hDDF := ((hf.fderiv_right (m:=∞) (by simp)).differentiableAt (by simp)).hasFDerivAt
  have hInv := (hasDerivAt_inv hpos.ne').comp_hasFDerivAt x hFD
  have hProduct := hInv.smul hDDF
  have hFunEq : (((fun y : ℝ => y⁻¹) ∘ f) • fderiv ℝ f) =
      (fun y => (f y)⁻¹ • fderiv ℝ f y) := by
    funext y
    rfl
  rw [hFunEq] at hProduct
  rw [hEq.fderiv_eq,hProduct.fderiv]
  calc
    _ ≤ ‖(f x)⁻¹ • fderiv ℝ (fderiv ℝ f) x‖+
        ‖((-((f x)^2)⁻¹) • fderiv ℝ f x).smulRight (fderiv ℝ f x)‖ := norm_add_le _ _
    _ = (f x)⁻¹*‖fderiv ℝ (fderiv ℝ f) x‖+((f x)^2)⁻¹*‖fderiv ℝ f x‖^2 := by
      rw [ContinuousLinearMap.norm_smulRight_apply]
      simp only [norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hpos),abs_neg,
        abs_of_nonneg (inv_nonneg.mpr (sq_nonneg (f x)))]
      ring
    _ ≤ _ := by gcongr

end ShrinkingSpheres
