import Proof.PoissonTaylorDerivative

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxSynthPendingDepth 30
open Set Filter
open scoped Topology
namespace ShrinkingSpheres

/-- Differentiating the genuine product Taylor remainder preserves its quadratic
    scale when the same factors and remainders satisfy the local budgets. -/
theorem norm_composition_taylor_remainder_derivative_le
    {P E F G : Type*}
    [NormedAddCommGroup P] [NormedSpace ℝ P]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    (A A1 : P → F →L[ℝ] G) (A0 : F →L[ℝ] G)
    (B B1 : P → E →L[ℝ] F) (B0 : E →L[ℝ] F)
    (x : P) (r CA DA DB V1 D1 CS DS DQ : ℝ)
    (hA : DifferentiableAt ℝ A x) (hA1 : DifferentiableAt ℝ A1 x)
    (hB : DifferentiableAt ℝ B x) (hB1 : DifferentiableAt ℝ B1 x)
    (hr : 0 ≤ r) (hr1 : r ≤ 1)
    (hCA : 0 ≤ CA) (hDA : 0 ≤ DA) (hDB : 0 ≤ DB)
    (hV1 : 0 ≤ V1) (hD1 : 0 ≤ D1) (hCS : 0 ≤ CS) (hDS : 0 ≤ DS) (hDQ : 0 ≤ DQ)
    (hNA : ‖A x‖ ≤ CA) (hDA' : ‖fderiv ℝ A x‖ ≤ DA*r)
    (hDB' : ‖A x-A0‖ ≤ DB*r)
    (hV1' : ‖B1 x‖ ≤ V1) (hD1' : ‖fderiv ℝ B1 x‖ ≤ D1)
    (hCS' : ‖B x-B0-r • B1 x‖ ≤ CS*r^2)
    (hDS' : ‖fderiv ℝ (fun p => B p-B0-r • B1 p) x‖ ≤ DS*r^2)
    (hDQ' : ‖fderiv ℝ (fun p => A p-A0-r • A1 p) x‖ ≤ DQ*r^2) :
    ‖fderiv ℝ (fun p => (A p).comp (B p)-A0.comp B0-
      r • (A0.comp (B1 p)+(A1 p).comp B0)) x‖ ≤
      (DA*CS+CA*DS+DA*V1+DB*D1+DQ*‖B0‖)*r^2 := by
  let S := fun p => B p-B0-r • B1 p
  let D := fun p => A p-A0
  let Q := fun p => A p-A0-r • A1 p
  have hS : DifferentiableAt ℝ S x := (hB.sub_const B0).sub (hB1.const_smul r)
  have hD : DifferentiableAt ℝ D x := hA.sub_const A0
  have hQ : DifferentiableAt ℝ Q x := (hA.sub_const A0).sub (hA1.const_smul r)
  have hId : (fun p => (A p).comp (B p)-A0.comp B0-
      r • (A0.comp (B1 p)+(A1 p).comp B0)) =
      fun p => (A p).comp (S p)+r • (D p).comp (B1 p)+(Q p).comp B0 := by
    funext p
    simp only [S,D,Q,ContinuousLinearMap.comp_sub,ContinuousLinearMap.sub_comp,
      ContinuousLinearMap.comp_smul,ContinuousLinearMap.smul_comp,smul_add]
    module
  rw [hId]
  have hFirst := norm_fderiv_clm_comp_le A S x hA hS
  have hSecond := norm_fderiv_clm_comp_le D B1 x hD hB1
  have hThird := norm_fderiv_clm_comp_le Q (fun _ : P => B0) x hQ (differentiableAt_const B0)
  simp only [fderiv_const_apply,norm_zero,mul_zero,add_zero] at hThird
  have hFull := (((hA.clm_comp hS).hasFDerivAt.add
    ((hD.clm_comp hB1).hasFDerivAt.const_smul r)).add
      (hQ.clm_comp (differentiableAt_const B0)).hasFDerivAt).fderiv
  change fderiv ℝ (fun p => (A p).comp (S p)+r • (D p).comp (B1 p)+(Q p).comp B0) x = _ at hFull
  rw [hFull]
  calc
    _ ≤ ‖fderiv ℝ (fun p => (A p).comp (S p)) x‖+
          ‖r • fderiv ℝ (fun p => (D p).comp (B1 p)) x‖+
          ‖fderiv ℝ (fun p => (Q p).comp B0) x‖ :=
      (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) (le_refl _))
    _ ≤ (DA*r)*(CS*r^2)+CA*(DS*r^2)+r*((DA*r)*V1+(DB*r)*D1)+(DQ*r^2)*‖B0‖ := by
      rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg hr]
      gcongr
      · exact hFirst.trans (by gcongr)
      · apply hSecond.trans
        rw [fderiv_sub_const]
        gcongr
      · exact hThird.trans (by gcongr)
    _ ≤ _ := by
      have hrr : r*r^2 ≤ r^2 := mul_le_of_le_one_left (sq_nonneg r) hr1
      nlinarith [mul_le_mul_of_nonneg_left hrr (mul_nonneg hDA hCS)]

end ShrinkingSpheres
