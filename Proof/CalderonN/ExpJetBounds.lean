module

public import Mathlib.Analysis.SpecialFunctions.Exp

public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Normed.Group.Defs

public import Proof.CalderonN.LogJetBounds
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

@[expose] public section

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxSynthPendingDepth 15
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Filter
open scoped ContDiff Topology
namespace CalderonN

lemma norm_fderiv_exp_comp_le {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (f : V → ℝ) (x : V) (hf : DifferentiableAt ℝ f x)
    (M : ℝ) (hM : ‖fderiv ℝ f x‖ ≤ M) :
    ‖fderiv ℝ (fun y => Real.exp (f y)) x‖ ≤ Real.exp (f x)*M := by
  rw [hf.hasFDerivAt.exp.fderiv,norm_smul,Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
  exact mul_le_mul_of_nonneg_left hM (Real.exp_pos _).le

/-- Second exponential jet estimate in the canonical Frechet derivative norm. -/
theorem norm_second_fderiv_exp_comp_le {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (f : V → ℝ) (x : V) (hf : ContDiffAt ℝ ∞ f x)
    (M1 M2 : ℝ) (hM1 : 0 ≤ M1) (hM2 : 0 ≤ M2)
    (hD : ‖fderiv ℝ f x‖ ≤ M1) (hDD : ‖fderiv ℝ (fderiv ℝ f) x‖ ≤ M2) :
    ‖fderiv ℝ (fderiv ℝ (fun y => Real.exp (f y))) x‖ ≤
      Real.exp (f x)*(M2+M1^2) := by
  have hNear := (hf.of_le (show (1:ℕ∞ω) ≤ ∞ by simp)).eventually (by simp)
  have hEq : fderiv ℝ (fun y => Real.exp (f y)) =ᶠ[𝓝 x]
      (fun y => Real.exp (f y) • fderiv ℝ f y) := by
    filter_upwards [hNear] with y hy
    exact ((hy.differentiableAt (by simp)).hasFDerivAt.exp).fderiv
  have hFD := (hf.differentiableAt (by simp)).hasFDerivAt
  have hDDF := ((hf.fderiv_right (m:=∞) (by simp)).differentiableAt (by simp)).hasFDerivAt
  have hProduct := hFD.exp.smul hDDF
  have hFunEq : ((fun y => Real.exp (f y)) • fderiv ℝ f) =
      (fun y => Real.exp (f y) • fderiv ℝ f y) := by funext y;rfl
  rw [hFunEq] at hProduct
  rw [hEq.fderiv_eq,hProduct.fderiv]
  calc
    _ ≤ ‖Real.exp (f x) • fderiv ℝ (fderiv ℝ f) x‖+
        ‖(Real.exp (f x) • fderiv ℝ f x).smulRight (fderiv ℝ f x)‖ := norm_add_le _ _
    _ = Real.exp (f x)*(‖fderiv ℝ (fderiv ℝ f) x‖+‖fderiv ℝ f x‖^2) := by
      rw [ContinuousLinearMap.norm_smulRight_apply]
      simp only [norm_smul,Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
      ring
    _ ≤ _ := by gcongr

end CalderonN
