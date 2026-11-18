import Proof.NormalMetricCovariantCenter

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set
open scoped ContDiff
namespace ShrinkingSpheres

lemma fderiv_normalMetricCovariantCenter (g : MetricField) (E : X × X → X) (y v a u w b : X)
    (hB : ContDiffAt ℝ ∞ (jointNormalMetricPair g E u w) (y,v))
    (hLeft : ContDiffAt ℝ ∞ (jointNormalMetricPair g E (connection g y a u) w) (y,v))
    (hRight : ContDiffAt ℝ ∞ (jointNormalMetricPair g E u (connection g y a w)) (y,v)) :
    fderiv ℝ (fun z => normalMetricCovariantCenter g E y z a u w) v b =
      fderiv ℝ (fderiv ℝ (jointNormalMetricPair g E u w)) (y,v) (0,b) (a,-connection g y a v)+
      fderiv ℝ (jointNormalMetricPair g E u w) (y,v) (0,-connection g y a b)-
      fderiv ℝ (jointNormalMetricPair g E (connection g y a u) w) (y,v) (0,b)-
      fderiv ℝ (jointNormalMetricPair g E u (connection g y a w)) (y,v) (0,b) := by
  have hInput : HasFDerivAt (fun z : X => (y,z)) (ContinuousLinearMap.inr ℝ X X) v :=
    (hasFDerivAt_const y v).prodMk (hasFDerivAt_id v)
  have hDB := ((hB.fderiv_right (m:=∞) (by simp)).differentiableAt (by simp)).hasFDerivAt.comp v hInput
  have hDirection : HasFDerivAt (fun z : X => (a,-connection g y a z))
      ((0 : X →L[ℝ] X).prod (-(connectionBilinear g y a))) v := by
    convert (hasFDerivAt_const a v).prodMk ((connectionBilinear g y a).hasFDerivAt.neg) using 1
    funext z
    simp only [Pi.neg_apply,connectionBilinear_apply]
  have hL := (hLeft.differentiableAt (by simp)).hasFDerivAt.comp v hInput
  have hR := (hRight.differentiableAt (by simp)).hasFDerivAt.comp v hInput
  have hAll := ((hDB.clm_apply hDirection).sub hL).sub hR
  have hh := congrArg (fun L : X →L[ℝ] ℝ => L b) hAll.fderiv
  simp only [Function.comp_def,_root_.sub_apply,_root_.add_apply,
    ContinuousLinearMap.comp_apply,ContinuousLinearMap.flip_apply,ContinuousLinearMap.prod_apply,
    ContinuousLinearMap.inr_apply,_root_.neg_apply,connectionBilinear_apply,
    zero_apply] at hh
  change fderiv ℝ (fun z => normalMetricCovariantCenter g E y z a u w) v b = _ at hh
  exact hh.trans (by ring)

/-- The true vertical derivative of the covariant center tensor vanishes
    linearly, supplying the angular half of its quadratic C1 remainder. -/
theorem Background.normal_metric_covariant_center_vertical_derivative_bound {Y Ω : Set X}
    (hY : IsOpen Y) (hΩ : IsOpen Ω) {K : ℝ} {m : ℕ} {M : Fin (m+1) → ℝ}
    {g g₁ g₂ : MetricField} {e : Frame} (h : Background Ω K M g g₁ g₂ e)
    (hK : 0 < K) (hm : 5 ≤ m) {expMap : X × X → X} {R : X → ℝ}
    (hN : NormalCoordinates Y Ω g expMap R) (hR : ContinuousOn R Y)
    {y : X} (hy : y ∈ Y) (v a u w b : X)
    (hv : metricPair g y v v < (R y)^2) (hv1 : ‖v‖ ≤ 1) :
    ‖fderiv ℝ (fun z => normalMetricCovariantCenter g expMap y z a u w) v b‖ ≤
      (1+4*(243*K*|M ⟨1,by omega⟩|))*backgroundJointNormalMetricJetBudget hm K M*
        ‖v‖*‖b‖*‖a‖*‖u‖*‖w‖ := by
  let Q := backgroundJointNormalMetricJetBudget hm K M
  let C := 243*K*|M ⟨1,by omega⟩|
  let B := jointNormalMetricPair g expMap u w
  let G := connection g y a
  have hC : 0 ≤ C := by dsimp [C];positivity
  have hEnvelope := backgroundExpJetEnvelope_ge_one hm hK.le M
  have hQ : 0 ≤ Q := by dsimp [Q,backgroundJointNormalMetricJetBudget];positivity
  have hG (z : X) : ‖G z‖ ≤ C*‖a‖*‖z‖ := by
    dsimp only [G]
    rw [← connectionBilinear_apply]
    exact (norm_bilinear_apply_le _ _ _).trans (by gcongr;exact h.connection_budget hK (by omega) (hN.center_mem hy))
  have hone : (1:ℝ) ∈ Icc (0:ℝ) 1 := ⟨zero_le_one,le_rfl⟩
  have hSegment := h.joint_normal_metric_segment_jets hY hΩ hK hm hN hR hy v u w hv hv1 g (by simp)
  have hB : ContDiffAt ℝ ∞ B (y,v) := by simpa only [one_smul] using (hSegment 1 hone).1
  have hBL : ContDiffAt ℝ ∞ (jointNormalMetricPair g expMap (G u) w) (y,v) := by
    simpa only [one_smul] using (h.joint_normal_metric_segment_jets hY hΩ hK hm hN hR hy v (G u) w hv hv1 g (by simp) 1 hone).1
  have hBR : ContDiffAt ℝ ∞ (jointNormalMetricPair g expMap u (G w)) (y,v) := by
    simpa only [one_smul] using (h.joint_normal_metric_segment_jets hY hΩ hK hm hN hR hy v u (G w) hv hv1 g (by simp) 1 hone).1
  have hD2 : ‖fderiv ℝ (fderiv ℝ B) (y,v)‖ ≤ Q*‖u‖*‖w‖ := by
    have hb := (hSegment 1 hone).2 2 (by omega)
    change ‖iteratedFDeriv ℝ 2 B (y,1 • v)‖ ≤ _ at hb
    simpa only [one_smul,← norm_iteratedFDeriv_fderiv (n:=1),norm_iteratedFDeriv_one] using hb
  have hMixed := (h.reference_normal_metric_center_taylor hY hΩ hK hm hN hR hy v u w a b hv hv1).2
  have hTwo : ‖fderiv ℝ (fderiv ℝ B) (y,v) (0,b) (0,-G v)‖ ≤
      Q*C*‖v‖*‖b‖*‖a‖*‖u‖*‖w‖ := by
    have hb := (ContinuousLinearMap.le_opNorm₂ (fderiv ℝ (fderiv ℝ B) (y,v)) ((0:X),b) ((0:X),-G v)).trans
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hD2 (norm_nonneg _)) (norm_nonneg _))
    simp only [Prod.norm_mk,norm_zero,max_eq_right (norm_nonneg b),norm_neg,max_eq_right (norm_nonneg (G v))] at hb
    exact hb.trans ((show (Q*‖u‖*‖w‖)*‖b‖*‖G v‖ ≤ (Q*‖u‖*‖w‖)*‖b‖*(C*‖a‖*‖v‖) by
      gcongr;exact hG v).trans_eq (by ring))
  have hThree : ‖fderiv ℝ B (y,v) (0,-G b)‖ ≤ Q*C*‖v‖*‖b‖*‖a‖*‖u‖*‖w‖ := by
    have hb := (h.reference_normal_metric_vertical_taylor hY hΩ hK hm hN hR hy v u w hv hv1).2 (-G b)
    rw [norm_neg] at hb
    exact hb.trans ((show Q*‖v‖*‖G b‖*‖u‖*‖w‖ ≤ Q*‖v‖*(C*‖a‖*‖b‖)*‖u‖*‖w‖ by
      gcongr;exact hG b).trans_eq (by ring))
  have hFour : ‖fderiv ℝ (jointNormalMetricPair g expMap (G u) w) (y,v) (0,b)‖ ≤
      Q*C*‖v‖*‖b‖*‖a‖*‖u‖*‖w‖ := by
    have hb := (h.reference_normal_metric_vertical_taylor hY hΩ hK hm hN hR hy v (G u) w hv hv1).2 b
    exact hb.trans ((show Q*‖v‖*‖b‖*‖G u‖*‖w‖ ≤ Q*‖v‖*‖b‖*(C*‖a‖*‖u‖)*‖w‖ by
      gcongr;exact hG u).trans_eq (by ring))
  have hFive : ‖fderiv ℝ (jointNormalMetricPair g expMap u (G w)) (y,v) (0,b)‖ ≤
      Q*C*‖v‖*‖b‖*‖a‖*‖u‖*‖w‖ := by
    have hb := (h.reference_normal_metric_vertical_taylor hY hΩ hK hm hN hR hy v u (G w) hv hv1).2 b
    exact hb.trans ((show Q*‖v‖*‖b‖*‖u‖*‖G w‖ ≤ Q*‖v‖*‖b‖*‖u‖*(C*‖a‖*‖w‖) by
      gcongr;exact hG w).trans_eq (by ring))
  rw [fderiv_normalMetricCovariantCenter g expMap y v a u w b hB hBL hBR]
  have hDir : (a,-G v) = ((a,0):X × X)+(0,-G v) := by simp
  change ‖fderiv ℝ (fderiv ℝ B) (y,v) (0,b) (a,-G v)+_ - _ - _‖ ≤ _
  rw [hDir,map_add]
  have hb := (norm_sub_le _ _).trans (add_le_add
    ((norm_sub_le _ _).trans (add_le_add ((norm_add_le _ _).trans (add_le_add
      ((norm_add_le _ _).trans (add_le_add hMixed hTwo)) hThree)) hFour)) hFive)
  exact hb.trans_eq (by dsimp only [Q,C];ring)

end ShrinkingSpheres
