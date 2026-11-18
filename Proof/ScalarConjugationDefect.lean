import Proof.NegativeCommutatorComposition
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1400000
namespace ShrinkingSpheres
lemma scalar_conjugation_adjoint_defect {D E F : Type*}
    [NormedAddCommGroup D] [NormedSpace ℝ D] [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (I0 : E →L[ℝ] F) (I1 : D →L[ℝ] F) (A B : D →L[ℝ] E)
    (M1 : D →L[ℝ] D) (M0 : E →L[ℝ] E) (MN K : F →L[ℝ] F)
    (hMN : MN.IsInvertible) (hFlux : A.comp M1=M0.comp B)
    (hCompat : I0.comp M0=MN.comp I0)
    (hComm : I0.comp (A.comp M1-M0.comp A)=K.comp I1) :
    I0.comp (A-B)=(-MN.inverse.comp K).comp I1 := by
  apply ContinuousLinearMap.ext
  intro u
  have hFluxu := congrArg (fun T : D →L[ℝ] E => T u) hFlux
  change A (M1 u)=M0 (B u) at hFluxu
  have hCompatv (v : E) : I0 (M0 v)=MN (I0 v) := congrArg (fun T : E →L[ℝ] F => T v) hCompat
  have hCommu := congrArg (fun T : D →L[ℝ] F => T u) hComm
  change I0 (A (M1 u)-M0 (A u))=K (I1 u) at hCommu
  rw [hFluxu,map_sub,hCompatv,hCompatv] at hCommu
  have hN : MN (I0 (A u-B u))=-(K (I1 u)) := by
    rw [map_sub,map_sub]
    exact eq_neg_of_add_eq_zero_left (by rw [← hCommu];abel)
  change I0 (A u-B u)=-(MN.inverse (K (I1 u)))
  calc
    _ = MN.inverse (MN (I0 (A u-B u))) := (hMN.inverse_apply_self _).symm
    _ = MN.inverse (-(K (I1 u))) := congrArg MN.inverse hN
    _ = _ := MN.inverse.map_neg _

lemma inverse_defect_identity {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (M : E →L[ℝ] E) (hM : M.IsInvertible) :
    ContinuousLinearMap.id ℝ E-M.inverse=M.inverse.comp (M-ContinuousLinearMap.id ℝ E) := by
  apply ContinuousLinearMap.ext
  intro u
  simp only [_root_.sub_apply,ContinuousLinearMap.id_apply,ContinuousLinearMap.comp_apply,map_sub,
    hM.inverse_apply_self]

lemma norm_conjugation_taylor_cancellation {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (M C R : E →L[ℝ] E) (hM : M.IsInvertible) (r CI BC CR : ℝ)
    (hr : 0 ≤ r) (hCI : 0 ≤ CI)
    (hInv : ‖M.inverse‖ ≤ CI) (hSmall : ‖M-ContinuousLinearMap.id ℝ E‖ ≤ BC*r)
    (hRest : ‖R‖ ≤ CR*r^2) :
    ‖-M.inverse.comp (r • C+R)+r • C‖ ≤ CI*(BC*‖C‖+CR)*r^2 := by
  have hId : ‖ContinuousLinearMap.id ℝ E-M.inverse‖ ≤ CI*BC*r := by
    rw [inverse_defect_identity M hM]
    exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
      ((mul_le_mul hInv hSmall (norm_nonneg _) hCI).trans_eq (by ring))
  have hEq : -M.inverse.comp (r • C+R)+r • C =
      r • ((ContinuousLinearMap.id ℝ E-M.inverse).comp C)-M.inverse.comp R := by
    simp only [ContinuousLinearMap.comp_add,ContinuousLinearMap.comp_smul,
      ContinuousLinearMap.sub_comp,ContinuousLinearMap.id_comp,smul_sub]
    abel
  rw [hEq]
  calc
    _ ≤ ‖r • ((ContinuousLinearMap.id ℝ E-M.inverse).comp C)‖+‖M.inverse.comp R‖ := norm_sub_le _ _
    _ = r*‖(ContinuousLinearMap.id ℝ E-M.inverse).comp C‖+‖M.inverse.comp R‖ := by
      rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg hr]
    _ ≤ r*((CI*BC*r)*‖C‖)+CI*(CR*r^2) := by
      apply add_le_add
      · exact mul_le_mul_of_nonneg_left ((ContinuousLinearMap.opNorm_comp_le _ _).trans
          (mul_le_mul_of_nonneg_right hId (norm_nonneg C))) hr
      · exact (ContinuousLinearMap.opNorm_comp_le _ _).trans (mul_le_mul hInv hRest (norm_nonneg _) hCI)
    _ = _ := by ring
end ShrinkingSpheres
