import Proof.PoissonTaylorDerivative
import Proof.OperatorInverseAffineTaylor

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxSynthPendingDepth 25
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter
open scoped Topology
namespace ShrinkingSpheres

/-- Differentiating the SAME canonical inverse Taylor remainder preserves
its quadratic gain. The actual inverse neighborhood is used in the identity. -/
theorem norm_operator_inverse_taylor_remainder_derivative_le
    {P E F : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    (A A1 : P → E →L[ℝ] F) (A0 : E →L[ℝ] F)
    (x : P) (U : Set P) (hU : IsOpen U) (hx : x ∈ U)
    (hA : DifferentiableAt ℝ A x) (hA1 : DifferentiableAt ℝ A1 x)
    (hI : DifferentiableAt ℝ (fun p => (A p).inverse) x)
    (hInv : ∀ p ∈ U,(A p).IsInvertible) (hInv0 : A0.IsInvertible)
    (r CI C0 DA DB V1 D1 DQ CS : ℝ)
    (hr : 0 ≤ r) (hr1 : r ≤ 1) (hCI : 0 ≤ CI) (hC0 : 0 ≤ C0)
    (hDA : 0 ≤ DA) (hDB : 0 ≤ DB) (hV1 : 0 ≤ V1) (hD1 : 0 ≤ D1) (hDQ : 0 ≤ DQ) (hCS : 0 ≤ CS)
    (hNI : ‖(A x).inverse‖ ≤ CI) (hNI0 : ‖A0.inverse‖ ≤ C0)
    (hNA : ‖fderiv ℝ A x‖ ≤ DA*r) (hNB : ‖A x-A0‖ ≤ DB*r)
    (hNV1 : ‖A1 x‖ ≤ V1) (hND1 : ‖fderiv ℝ A1 x‖ ≤ D1)
    (hNDQ : ‖fderiv ℝ (fun p => A p-A0-r • A1 p) x‖ ≤ DQ*r^2)
    (hNS : ‖(A x).inverse-A0.inverse-r • (-(A0.inverse.comp ((A1 x).comp A0.inverse)))‖ ≤ CS*r^2) :
    ‖fderiv ℝ (fun p => (A p).inverse-A0.inverse-
      r • (-(A0.inverse.comp ((A1 p).comp A0.inverse)))) x‖ ≤
      CI*((DQ+DA*C0*V1+DB*C0*D1)*C0+DA*CS)*r^2 := by
  let J1 := fun p => -(A0.inverse.comp ((A1 p).comp A0.inverse))
  let S := fun p => -((A p).inverse-A0.inverse-r • J1 p)
  have hJ1 : DifferentiableAt ℝ J1 x :=
    ((differentiableAt_const A0.inverse).clm_comp (hA1.clm_comp (differentiableAt_const A0.inverse))).neg
  have hS : DifferentiableAt ℝ S x := ((hI.sub_const A0.inverse).sub (hJ1.const_smul r)).neg
  have hResolvent (p : P) (hp : p ∈ U) :
      A0.inverse-(A p).inverse = (A p).inverse.comp ((A p-A0).comp A0.inverse) := by
    apply ContinuousLinearMap.ext
    intro f
    have hEq := inverse_sub_inverse_apply (A p) A0 (hInv p hp) hInv0 f
    have hNeg : (A p-A0) (A0.inverse f) = -((A0-A p) (A0.inverse f)) := by
      simp only [sub_apply]
      abel
    change A0.inverse f-(A p).inverse f = (A p).inverse ((A p-A0) (A0.inverse f))
    rw [hNeg,map_neg]
    exact (show A0.inverse f-(A p).inverse f = -((A p).inverse f-A0.inverse f) by abel).trans (congrArg Neg.neg hEq)
  have hActual (p : P) (hp : p ∈ U) : S p =
      (A p).inverse.comp ((A p-A0).comp A0.inverse)-r • A0.inverse.comp ((A1 p).comp A0.inverse) := by
    rw [← hResolvent p hp]
    dsimp only [S,J1]
    module
  have hQ : DifferentiableAt ℝ (fun p => (A p-A0)-0-r • A1 p) x :=
    (((hA.sub_const A0).sub_const 0).sub (hA1.const_smul r))
  have hPoint : ‖S x‖ ≤ CS*r^2 := by simpa only [S,norm_neg] using hNS
  have hResult := norm_poisson_taylor_remainder_derivative_le A A0 (fun p => A p-A0) A1 0 A0.inverse S
    r x U hU hx hA hA1 hQ hS hInv hInv0 (by simp) hActual
    CI C0 DA DB V1 D1 DQ CS hr hr1 hCI hC0 hDA hDB hV1 hD1 hDQ hCS hNI hNI0 hNA hNB hNV1 hND1
    (by simpa only [sub_zero] using hNDQ) hPoint
  have hBound : ‖fderiv ℝ (fun p => (A p).inverse-A0.inverse-r • J1 p) x‖ ≤
      CI*((DQ+DA*C0*V1+DB*C0*D1)*‖A0.inverse‖+DA*CS)*r^2 := by
    simpa only [S,fderiv_fun_neg,norm_neg] using hResult
  exact hBound.trans (by gcongr)

end ShrinkingSpheres
