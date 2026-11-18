import Proof.PoissonTaylorDerivative

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option maxSynthPendingDepth 30
open Set Filter
open scoped Topology
namespace ShrinkingSpheres

/-- One exact affine family identity propagates the same first-model and
    quadratic-residual derivative budgets to the actual principal family. -/
theorem affine_family_derivative_budget
    {P V : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    (A A1 R : P → V) (A0 : V) (x : P) (r D1 DQ : ℝ)
    (hFamily : ∀ p,A p = A0+r • A1 p+R p)
    (hA1 : DifferentiableAt ℝ A1 x) (hR : DifferentiableAt ℝ R x)
    (hr : 0 ≤ r) (hr1 : r ≤ 1) (hD1 : 0 ≤ D1) (hDQ : 0 ≤ DQ)
    (hND1 : ‖fderiv ℝ A1 x‖ ≤ D1) (hNDQ : ‖fderiv ℝ R x‖ ≤ DQ*r^2) :
    ‖fderiv ℝ A x‖ ≤ (D1+DQ)*r ∧
      ‖fderiv ℝ (fun p => A p-A0-r • A1 p) x‖ ≤ DQ*r^2 := by
  have hEq : A = fun p => A0+r • A1 p+R p := funext hFamily
  have hD : HasFDerivAt (fun p => A0+r • A1 p+R p)
      (r • fderiv ℝ A1 x+fderiv ℝ R x) x := by
    have h := ((hasFDerivAt_const A0 x).add (hA1.hasFDerivAt.const_smul r)).add hR.hasFDerivAt
    change HasFDerivAt (fun p => A0+r • A1 p+R p)
      (0+r • fderiv ℝ A1 x+fderiv ℝ R x) x at h
    simpa only [zero_add] using h
  have hAD : fderiv ℝ A x = r • fderiv ℝ A1 x+fderiv ℝ R x :=
    (congrArg (fun f : P → V => fderiv ℝ f x) hEq).trans hD.fderiv
  have hResidual : (fun p => A p-A0-r • A1 p) = R := by
    funext p
    rw [hFamily p]
    module
  constructor
  · rw [hAD]
    calc
      _ ≤ ‖r • fderiv ℝ A1 x‖+‖fderiv ℝ R x‖ := norm_add_le _ _
      _ ≤ r*D1+DQ*r^2 := by
        rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg hr]
        exact add_le_add (mul_le_mul_of_nonneg_left hND1 hr) hNDQ
      _ ≤ _ := by
        have hrr : r^2 ≤ r := by nlinarith
        nlinarith [mul_le_mul_of_nonneg_left hrr hDQ]
  · exact (congrArg (fun f : P → V => ‖fderiv ℝ f x‖) hResidual).le.trans hNDQ

end ShrinkingSpheres
