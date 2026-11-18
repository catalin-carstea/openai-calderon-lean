import Proof.RadialAdjointTaylorCancellation
import Proof.PoissonTaylorDerivative

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxSynthPendingDepth 25
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace ShrinkingSpheres

/-- Differentiating the cancelled forcing uses only the forward remainder
    jet and the coarse/H1 boundary coefficient remainder jets. -/
theorem norm_radialAdjointTaylorForcing_derivative_le
    {P E H : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup H] [NormedSpace ℝ H]
    (M0 M01 : P → E →L[ℝ] E) (M1 M11 : P → H →L[ℝ] H)
    (D D1 T Td : P → H →L[ℝ] E) (D0 : H →L[ℝ] E) (x : P) (r C q : ℝ)
    (hr : 0 ≤ r) (hr1 : r ≤ 1) (hC : 0 ≤ C) (hq : 0 ≤ q)
    (hM0 : DifferentiableAt ℝ M0 x) (hM01 : DifferentiableAt ℝ M01 x)
    (hM1 : DifferentiableAt ℝ M1 x) (hM11 : DifferentiableAt ℝ M11 x)
    (hD : DifferentiableAt ℝ D x) (hD1 : DifferentiableAt ℝ D1 x)
    (hT : DifferentiableAt ℝ T x) (hTd : DifferentiableAt ℝ Td x)
    (hNM0 : ‖M0 x‖ ≤ C) (hND0 : ‖D0‖ ≤ 2) (hND1 : ‖D1 x‖ ≤ C)
    (hNJ : ‖D x-D0-r • D1 x‖ ≤ C*r^2)
    (hDel : ‖M0 x-ContinuousLinearMap.id ℝ E‖ ≤ C*r)
    (hDM0 : ‖fderiv ℝ M0 x‖ ≤ q*r)
    (hDJ : ‖fderiv ℝ (fun p => D p-D0-r • D1 p) x‖ ≤ q*r^2)
    (hDQ0 : ‖fderiv ℝ (fun p => M0 p-ContinuousLinearMap.id ℝ E-r • M01 p) x‖ ≤ q*r^2)
    (hDQ1 : ‖fderiv ℝ (fun p => M1 p-ContinuousLinearMap.id ℝ H-r • M11 p) x‖ ≤ q*r^2)
    (hDD1 : ‖fderiv ℝ D1 x‖ ≤ q)
    (hDT : ‖fderiv ℝ T x‖ ≤ q*r^2) (hDTd : ‖fderiv ℝ Td x‖ ≤ q*r^2) :
    ‖fderiv ℝ (fun p => radialAdjointTaylorForcing
      (M0 p) (M01 p) (M1 p) (M11 p) (D p) D0 (D1 p) (T p) (Td p) r) x‖ ≤
      (4*C+6)*q*r^2 := by
  let J := fun p => D p-D0-r • D1 p
  let Q0 := fun p => M0 p-ContinuousLinearMap.id ℝ E-r • M01 p
  let Q1 := fun p => M1 p-ContinuousLinearMap.id ℝ H-r • M11 p
  let B := fun p => M0 p-ContinuousLinearMap.id ℝ E
  have hJ : DifferentiableAt ℝ J x := (hD.sub (differentiableAt_const _)).sub (hD1.const_smul r)
  have hQ0 : DifferentiableAt ℝ Q0 x := (hM0.sub (differentiableAt_const _)).sub (hM01.const_smul r)
  have hQ1 : DifferentiableAt ℝ Q1 x := (hM1.sub (differentiableAt_const _)).sub (hM11.const_smul r)
  have hB : DifferentiableAt ℝ B x := hM0.sub (differentiableAt_const _)
  let A := fun p => (M0 p).comp (J p)
  let V := fun p => (Q0 p).comp D0
  let W := fun p => D0.comp (Q1 p)
  let G := fun p => (B p).comp (D1 p)
  have hA := hM0.clm_comp hJ
  have hV := hQ0.clm_comp (differentiableAt_const D0)
  have hW := (differentiableAt_const D0).clm_comp hQ1
  have hG := hB.clm_comp hD1
  have hR2 : r*r^2 ≤ r^2 := mul_le_of_le_one_left (sq_nonneg r) hr1
  have hABound : ‖fderiv ℝ A x‖ ≤ 2*C*q*r^2 := by
    have h := norm_fderiv_clm_comp_le M0 J x hM0 hJ
    calc
      _ ≤ (q*r)*(C*r^2)+C*(q*r^2) := h.trans (by gcongr)
      _ = (C*q)*(r*r^2)+(C*q)*r^2 := by ring
      _ ≤ (C*q)*r^2+(C*q)*r^2 := by gcongr
      _ = _ := by ring
  have hVBound : ‖fderiv ℝ V x‖ ≤ 2*q*r^2 := by
    have h := norm_fderiv_clm_comp_le Q0 (fun _ : P => D0) x hQ0 (differentiableAt_const _)
    simp only [fderiv_const_apply,norm_zero,mul_zero,add_zero] at h
    exact h.trans ((mul_le_mul hDQ0 hND0 (norm_nonneg _) (by positivity)).trans_eq (by ring))
  have hWBound : ‖fderiv ℝ W x‖ ≤ 2*q*r^2 := by
    have h := norm_fderiv_clm_comp_le (fun _ : P => D0) Q1 x (differentiableAt_const _) hQ1
    simp only [fderiv_const_apply,norm_zero,zero_mul,zero_add] at h
    exact h.trans ((mul_le_mul hND0 hDQ1 (norm_nonneg _) (by norm_num)).trans_eq (by ring))
  have hGBound : ‖r • fderiv ℝ G x‖ ≤ 2*C*q*r^2 := by
    have h := norm_fderiv_clm_comp_le B D1 x hB hD1
    have hDB : ‖fderiv ℝ B x‖ ≤ q*r := by rw [fderiv_sub_const];exact hDM0
    rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg hr]
    have hProd : ‖fderiv ℝ G x‖ ≤ (q*r)*C+(C*r)*q := h.trans (by gcongr)
    exact (mul_le_mul_of_nonneg_left hProd hr).trans_eq (by ring)
  have hDer := (((((hA.hasFDerivAt.add hV.hasFDerivAt).sub hW.hasFDerivAt).add
    (hG.hasFDerivAt.const_smul r)).add hT.hasFDerivAt).sub hTd.hasFDerivAt).fderiv
  apply (congrArg norm hDer).le.trans
  let a := fderiv ℝ A x
  let v := fderiv ℝ V x
  let w := fderiv ℝ W x
  let g := r • fderiv ℝ G x
  let t := fderiv ℝ T x
  let td := fderiv ℝ Td x
  have hn1 := norm_add_le a v
  have hn2 := norm_sub_le (a+v) w
  have hn3 := norm_add_le (a+v-w) g
  have hn4 := norm_add_le (a+v-w+g) t
  have hn5 := norm_sub_le (a+v-w+g+t) td
  change ‖a+v-w+g+t-td‖ ≤ _
  nlinarith only [hn1,hn2,hn3,hn4,hn5,hABound,hVBound,hWBound,hGBound,hDT,hDTd]

end ShrinkingSpheres
