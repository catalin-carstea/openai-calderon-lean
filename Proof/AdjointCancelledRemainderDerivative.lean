import Proof.PoissonTaylorDerivative

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxSynthPendingDepth 25
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter
open scoped Topology
namespace ShrinkingSpheres

def radialAdjointJetBudget (C : ℝ) : ℝ := 2*C^4+7*C^3+4*C^2+7*C

lemma radialAdjointJetBudget_nonneg (C : ℝ) (hC : 0 ≤ C) : 0 ≤ radialAdjointJetBudget C := by
  unfold radialAdjointJetBudget
  positivity

/-- The cancelled adjoint remainder has a quadratic derivative from forward
    and coefficient forcing jets and a radius-linear first inverse derivative. -/
theorem norm_adjoint_cancelled_remainder_derivative_le
    {P E H : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup H] [NormedSpace ℝ H]
    (F Ba R : P → H →L[ℝ] E) (Inv : P → H →L[ℝ] H) (x : P) (r C q : ℝ)
    (hr : 0 ≤ r) (hr1 : r ≤ 1) (hC : 0 ≤ C) (hq : 0 ≤ q)
    (hF : DifferentiableAt ℝ F x) (hBa : DifferentiableAt ℝ Ba x) (hInv : DifferentiableAt ℝ Inv x)
    (hIdentity : R =ᶠ[𝓝 x] (fun p => (F p).comp (Inv p)+r • (Ba p).comp (Inv p-ContinuousLinearMap.id ℝ H)))
    (hNF : ‖F x‖ ≤ (2*C^2+6*C)*r^2)
    (hDF : ‖fderiv ℝ F x‖ ≤ (4*C+6)*q*r^2)
    (hNI : ‖Inv x‖ ≤ C) (hDI : ‖fderiv ℝ Inv x‖ ≤ C^2*q*r)
    (hIDiff : ‖Inv x-ContinuousLinearMap.id ℝ H‖ ≤ C*r)
    (hNB : ‖Ba x‖ ≤ C) (hDB : ‖fderiv ℝ Ba x‖ ≤ q) :
    ‖fderiv ℝ R x‖ ≤ radialAdjointJetBudget C*q*r^2 := by
  let V := fun p => Inv p-ContinuousLinearMap.id ℝ H
  have hV : DifferentiableAt ℝ V x := hInv.sub (differentiableAt_const _)
  have hDV : ‖fderiv ℝ V x‖ ≤ C^2*q*r := by rw [fderiv_sub_const];exact hDI
  have hOne := norm_fderiv_clm_comp_le F Inv x hF hInv
  have hTwo := norm_fderiv_clm_comp_le Ba V x hBa hV
  have hR2 : r*r^2 ≤ r^2 := mul_le_of_le_one_left (sq_nonneg r) hr1
  have hOneBound : ‖fderiv ℝ (fun p => (F p).comp (Inv p)) x‖ ≤
      ((4*C+6)*C+(2*C^2+6*C)*C^2)*q*r^2 := by
    calc
      _ ≤ ((4*C+6)*q*r^2)*C+((2*C^2+6*C)*r^2)*(C^2*q*r) := hOne.trans (by gcongr)
      _ = ((4*C+6)*C)*q*r^2+((2*C^2+6*C)*C^2*q)*(r*r^2) := by ring
      _ ≤ ((4*C+6)*C)*q*r^2+((2*C^2+6*C)*C^2*q)*r^2 := by gcongr
      _ = _ := by ring
  have hTwoBound : ‖r • fderiv ℝ (fun p => (Ba p).comp (V p)) x‖ ≤ (C+C^3)*q*r^2 := by
    rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg hr]
    have hProd : ‖fderiv ℝ (fun p => (Ba p).comp (V p)) x‖ ≤ q*(C*r)+C*(C^2*q*r) :=
      hTwo.trans (by gcongr)
    exact (mul_le_mul_of_nonneg_left hProd hr).trans_eq (by ring)
  rw [hIdentity.fderiv_eq]
  have hD := ((hF.clm_comp hInv).hasFDerivAt.add
    ((hBa.clm_comp hV).hasFDerivAt.const_smul r)).fderiv
  exact (congrArg norm hD).le.trans ((norm_add_le _ _).trans
    ((add_le_add hOneBound hTwoBound).trans_eq (by unfold radialAdjointJetBudget;ring)))

end ShrinkingSpheres
