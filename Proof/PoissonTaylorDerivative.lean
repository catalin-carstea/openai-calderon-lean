module

public import Proof.RectangularImplicitOperatorDerivative
public import Proof.PoissonFirstVariationBound
public import Mathlib.Analysis.Calculus.FDeriv.Add

@[expose] public section

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Filter Set
open scoped Topology
namespace ShrinkingSpheres

lemma norm_fderiv_clm_comp_le {P E F G : Type*}
    [NormedAddCommGroup P] [NormedSpace ℝ P]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    (A : P → F →L[ℝ] G) (B : P → E →L[ℝ] F) (x : P)
    (hA : DifferentiableAt ℝ A x) (hB : DifferentiableAt ℝ B x) :
    ‖fderiv ℝ (fun p => (A p).comp (B p)) x‖ ≤
      ‖fderiv ℝ A x‖*‖B x‖+‖A x‖*‖fderiv ℝ B x‖ := by
  have hD := (hA.hasFDerivAt.clm_comp hB.hasFDerivAt).fderiv
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro b
  have hAt : fderiv ℝ (fun p => (A p).comp (B p)) x b =
      (A x).comp (fderiv ℝ B x b)+(fderiv ℝ A x b).comp (B x) := by
    simpa only [_root_.add_apply,ContinuousLinearMap.comp_apply,ContinuousLinearMap.flip_apply,
      ContinuousLinearMap.compL_apply] using congrArg (fun L : P →L[ℝ] E →L[ℝ] G => L b) hD
  rw [hAt]
  calc
    _ ≤ ‖A x‖*‖fderiv ℝ B x b‖+‖fderiv ℝ A x b‖*‖B x‖ :=
      (norm_add_le _ _).trans (add_le_add (ContinuousLinearMap.opNorm_comp_le _ _)
        (ContinuousLinearMap.opNorm_comp_le _ _))
    _ ≤ ‖A x‖*(‖fderiv ℝ B x‖*‖b‖)+(‖fderiv ℝ A x‖*‖b‖)*‖B x‖ := by
      gcongr
      exact ContinuousLinearMap.le_opNorm _ _
      exact ContinuousLinearMap.le_opNorm _ _
    _ = _ := by ring

/-- The true inverse-based Poisson Taylor remainder satisfies a local left
    identity whose forcing retains its quadratic smallness under differentiation.
    No derivative of the inverse is estimated separately. -/
theorem norm_poisson_taylor_remainder_derivative_le
    {P Z E F H : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup H] [NormedSpace ℝ H]
    (A : P → Z →L[ℝ] F) (A0 : Z →L[ℝ] F)
    (T T1 : P → E →L[ℝ] F) (T0 : E →L[ℝ] F) (P0 : H →L[ℝ] E)
    (S : P → H →L[ℝ] Z) (r : ℝ) (x : P) (U : Set P) (hU : IsOpen U) (hx : x ∈ U)
    (hA : DifferentiableAt ℝ A x) (hT1 : DifferentiableAt ℝ T1 x)
    (hQ : DifferentiableAt ℝ (fun p => T p-T0-r • T1 p) x)
    (hS : DifferentiableAt ℝ S x)
    (hInv : ∀ p ∈ U,(A p).IsInvertible) (hInv0 : A0.IsInvertible)
    (hFlat : T0.comp P0 = 0)
    (hActual : ∀ p ∈ U,S p = (A p).inverse.comp ((T p).comp P0)-
      r • A0.inverse.comp ((T1 p).comp P0))
    (CI C0 DA DB V1 D1 DQ CS : ℝ)
    (hr : 0 ≤ r) (hr1 : r ≤ 1)
    (hCI : 0 ≤ CI) (hC0 : 0 ≤ C0) (hDA : 0 ≤ DA) (hDB : 0 ≤ DB)
    (hV1 : 0 ≤ V1) (hD1 : 0 ≤ D1) (hDQ : 0 ≤ DQ) (hCS : 0 ≤ CS)
    (hNI : ‖(A x).inverse‖ ≤ CI) (hNI0 : ‖A0.inverse‖ ≤ C0)
    (hNA : ‖fderiv ℝ A x‖ ≤ DA*r) (hNB : ‖A x-A0‖ ≤ DB*r)
    (hNV1 : ‖T1 x‖ ≤ V1) (hND1 : ‖fderiv ℝ T1 x‖ ≤ D1)
    (hNDQ : ‖fderiv ℝ (fun p => T p-T0-r • T1 p) x‖ ≤ DQ*r^2)
    (hNS : ‖S x‖ ≤ CS*r^2) :
    ‖fderiv ℝ S x‖ ≤ CI*((DQ+DA*C0*V1+DB*C0*D1)*‖P0‖+DA*CS)*r^2 := by
  let Q := fun p => T p-T0-r • T1 p
  let B := fun p => A p-A0
  let L := fun p => A0.inverse.comp ((T1 p).comp P0)
  let R := fun p => (Q p).comp P0-r • (B p).comp (L p)
  have hB : DifferentiableAt ℝ B x := (hA.hasFDerivAt.sub_const A0).differentiableAt
  have hL : DifferentiableAt ℝ L x := (differentiableAt_const A0.inverse).clm_comp
    (hT1.clm_comp (differentiableAt_const P0))
  have hIdentity : (fun p => (A p).comp (S p)) =ᶠ[𝓝 x] R := by
    filter_upwards [hU.mem_nhds hx] with p hp
    rw [hActual p hp]
    ext f
    have hZero : T0 (P0 f) = 0 := congrArg (fun M : H →L[ℝ] F => M f) hFlat
    have hCancel := (hInv p hp).self_apply_inverse ((T p) (P0 f))
    have hCancel0 := hInv0.self_apply_inverse ((T1 p) (P0 f))
    simp only [ContinuousLinearMap.comp_apply,ContinuousLinearMap.sub_apply,
      ContinuousLinearMap.smul_apply,map_sub,map_smul,R,Q,B,L,hZero,map_zero,sub_zero] at *
    rw [hCancel]
    rw [hCancel0]
    module
  have hNL : ‖L x‖ ≤ C0*V1*‖P0‖ := by
    calc
      _ ≤ ‖A0.inverse‖*(‖T1 x‖*‖P0‖) :=
        (ContinuousLinearMap.opNorm_comp_le _ _).trans
          (mul_le_mul_of_nonneg_left (ContinuousLinearMap.opNorm_comp_le _ _) (norm_nonneg _))
      _ ≤ C0*(V1*‖P0‖) := by gcongr
      _ = _ := by ring
  have hDL : ‖fderiv ℝ L x‖ ≤ C0*D1*‖P0‖ := by
    have h1 := norm_fderiv_clm_comp_le T1 (fun _ : P => P0) x hT1 (differentiableAt_const P0)
    have h2 := norm_fderiv_clm_comp_le (fun _ : P => A0.inverse)
      (fun p => (T1 p).comp P0) x (differentiableAt_const A0.inverse) (hT1.clm_comp (differentiableAt_const P0))
    try simp only [fderiv_const_apply,norm_zero,mul_zero,zero_mul,add_zero,zero_add] at h1 h2
    have hInner : ‖fderiv ℝ (fun p => (T1 p).comp P0) x‖ ≤ D1*‖P0‖ :=
      h1.trans (mul_le_mul_of_nonneg_right hND1 (norm_nonneg P0))
    exact h2.trans ((mul_le_mul hNI0 hInner (norm_nonneg _) hC0).trans_eq (by ring))
  have hDR : ‖fderiv ℝ R x‖ ≤
      (DQ+DA*C0*V1+DB*C0*D1)*‖P0‖*r^2 := by
    have hLeft := norm_fderiv_clm_comp_le Q (fun _ : P => P0) x hQ (differentiableAt_const P0)
    have hRight := norm_fderiv_clm_comp_le B L x hB hL
    try simp only [fderiv_const_apply,norm_zero,mul_zero,add_zero] at hLeft
    have hNR : fderiv ℝ R x = fderiv ℝ (fun p => (Q p).comp P0) x-
        r • fderiv ℝ (fun p => (B p).comp (L p)) x := by
      exact ((hQ.clm_comp (differentiableAt_const P0)).hasFDerivAt.sub
        ((hB.clm_comp hL).hasFDerivAt.const_smul r)).fderiv
    rw [hNR]
    calc
      _ ≤ ‖fderiv ℝ (fun p => (Q p).comp P0) x‖+
          ‖r • fderiv ℝ (fun p => (B p).comp (L p)) x‖ := norm_sub_le _ _
      _ ≤ (DQ*r^2)*‖P0‖+r*((DA*r)*(C0*V1*‖P0‖)+(DB*r)*(C0*D1*‖P0‖)) := by
        rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg hr]
        gcongr
        exact hLeft.trans (by gcongr)
        apply hRight.trans
        rw [fderiv_sub_const]
        gcongr
      _ = _ := by ring
  have hBound := norm_operator_derivative_of_rectangular_left_identity A S R x hA hS hIdentity
    (hInv x hx) CI (DA*r) (CS*r^2)
    ((DQ+DA*C0*V1+DB*C0*D1)*‖P0‖*r^2) hCI (by positivity) (by positivity)
    (by positivity) hNI hNA hNS hDR
  apply hBound.trans
  have hRR : r*r^2 ≤ r^2 := by nlinarith [sq_nonneg r]
  nlinarith [mul_le_mul_of_nonneg_left hRR (mul_nonneg hCI (mul_nonneg hDA hCS))]

end ShrinkingSpheres
