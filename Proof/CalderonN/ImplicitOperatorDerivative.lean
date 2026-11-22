module

public import Proof.CalderonN.LocalFlowVariation
import Mathlib.Analysis.Calculus.FDeriv.CompCLM
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Invertible

import Mathlib.Tactic

/-! Adapted from the checked Proposition 5.3 release, Proof/ImplicitOperatorDerivative.lean. -/

public section

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open Filter
open scoped Topology
namespace CalderonN

variable {dim : ℕ} [NeZero dim]

/-- Differentiate an actual local operator identity A H = R and solve on the
    left. This keeps the derivative estimate sensitive to the small factor H. -/
theorem norm_operator_derivative_of_left_identity
    {P E : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (A H R : P → E →L[ℝ] E) (x : P)
    (hA : DifferentiableAt ℝ A x) (hH : DifferentiableAt ℝ H x)
    (hIdentity : (fun y => (A y).comp (H y)) =ᶠ[𝓝 x] R)
    (hInv : (A x).IsInvertible) (CI DA VH DR : ℝ)
    (hCI : 0 ≤ CI) (hDA : 0 ≤ DA) (hVH : 0 ≤ VH) (hDR : 0 ≤ DR)
    (hNI : ‖(A x).inverse‖ ≤ CI) (hNA : ‖fderiv ℝ A x‖ ≤ DA)
    (hNH : ‖H x‖ ≤ VH) (hNR : ‖fderiv ℝ R x‖ ≤ DR) :
    ‖fderiv ℝ H x‖ ≤ CI*(DR+DA*VH) := by
  have hProduct := hA.hasFDerivAt.clm_comp hH.hasFDerivAt
  have hDerivative := hProduct.fderiv.symm.trans hIdentity.fderiv_eq
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro b
  have hAt : (A x).comp (fderiv ℝ H x b)+(fderiv ℝ A x b).comp (H x) = fderiv ℝ R x b := by
    simpa only [_root_.add_apply,ContinuousLinearMap.comp_apply,ContinuousLinearMap.flip_apply,
      ContinuousLinearMap.compL_apply] using
        congrArg (fun L : P →L[ℝ] E →L[ℝ] E => L b) hDerivative
  have hCancel : fderiv ℝ R x b-(fderiv ℝ A x b).comp (H x) = (A x).comp (fderiv ℝ H x b) := by
    rw [← hAt]
    abel
  have hSolve : fderiv ℝ H x b = (A x).inverse.comp
      (fderiv ℝ R x b-(fderiv ℝ A x b).comp (H x)) := by
    rw [hCancel,← ContinuousLinearMap.comp_assoc,hInv.inverse_comp_self,ContinuousLinearMap.id_comp]
  have hAb : ‖fderiv ℝ A x b‖ ≤ DA*‖b‖ :=
    (ContinuousLinearMap.le_opNorm _ _).trans (mul_le_mul_of_nonneg_right hNA (norm_nonneg b))
  have hRb : ‖fderiv ℝ R x b‖ ≤ DR*‖b‖ :=
    (ContinuousLinearMap.le_opNorm _ _).trans (mul_le_mul_of_nonneg_right hNR (norm_nonneg b))
  rw [hSolve]
  calc
    _ ≤ ‖(A x).inverse‖*‖fderiv ℝ R x b-(fderiv ℝ A x b).comp (H x)‖ :=
      ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ CI*(‖fderiv ℝ R x b‖+‖(fderiv ℝ A x b).comp (H x)‖) := by
      exact mul_le_mul hNI (norm_sub_le _ _) (norm_nonneg _) hCI
    _ ≤ CI*(DR*‖b‖+(DA*‖b‖)*VH) := by
      gcongr
      exact (ContinuousLinearMap.opNorm_comp_le _ _).trans (by gcongr)
    _ = _ := by ring

end CalderonN
