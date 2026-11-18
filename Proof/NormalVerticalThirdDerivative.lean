import Proof.NormalJointEndpointJets
import Proof.NormalJacobianSecondDerivative

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1400000
set_option maxSynthPendingDepth 20
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter
open scoped ContDiff Topology
namespace ShrinkingSpheres

lemma fderiv_normalVerticalJacobian_apply (expMap : X × X → X) (y v a b : X)
    (hE : ContDiffAt ℝ ∞ expMap (y,v)) :
    fderiv ℝ (normalVerticalJacobian expMap y) v a b =
      fderiv ℝ (fderiv ℝ expMap) (y,v) (0,a) (0,b) := by
  have hInput : HasFDerivAt (fun w : X => (y,w)) (ContinuousLinearMap.inr ℝ X X) v :=
    (hasFDerivAt_const y v).prodMk (hasFDerivAt_id v)
  have hD := ((hE.fderiv_right (m:=∞) (by simp)).differentiableAt (by simp)).hasFDerivAt.comp v hInput
  have hJ := hD.clm_comp (hasFDerivAt_const (ContinuousLinearMap.inr ℝ X X) v)
  change HasFDerivAt (normalVerticalJacobian expMap y) _ v at hJ
  rw [hJ.fderiv]
  simp only [_root_.add_apply,ContinuousLinearMap.comp_apply,ContinuousLinearMap.flip_apply,
    ContinuousLinearMap.compL_apply,ContinuousLinearMap.inr_apply,zero_apply,map_zero,zero_add]

lemma NormalCoordinates.second_fderiv_normalVerticalJacobian_apply {Y Ω : Set X} {g : MetricField}
    {expMap : X × X → X} {R : X → ℝ} (hN : NormalCoordinates Y Ω g expMap R)
    {y : X} (hy : y ∈ Y) (v a b c : X) (hv : v ∈ disk g y (R y)) :
    fderiv ℝ (fderiv ℝ (normalVerticalJacobian expMap y)) v a b c =
      fderiv ℝ (fderiv ℝ (fderiv ℝ expMap)) (y,v) (0,a) (0,b) (0,c) := by
  obtain ⟨U,hU,hTube,hReg⟩ := hN.1
  have hMem : (y,v) ∈ U := hTube ⟨hy,hv⟩
  have hE : ContDiffAt ℝ ∞ expMap (y,v) := hReg.contDiffAt (hU.mem_nhds hMem)
  have hInput : HasFDerivAt (fun w : X => (y,w)) (ContinuousLinearMap.inr ℝ X X) v :=
    (hasFDerivAt_const y v).prodMk (hasFDerivAt_id v)
  have hDD := (((hE.fderiv_right (m:=∞) (by simp)).fderiv_right (m:=∞) (by simp)).differentiableAt
    (by simp)).hasFDerivAt.comp v hInput
  have hEval := (hDD.clm_apply (hasFDerivAt_const ((0:X),b) v)).clm_apply (hasFDerivAt_const ((0:X),c) v)
  simp only [Function.comp_def] at hEval
  have hNear : (fun w => fderiv ℝ (normalVerticalJacobian expMap y) w b c) =ᶠ[𝓝 v]
      (fun w => fderiv ℝ (fderiv ℝ expMap) (y,w) (0,b) (0,c)) := by
    have hUInput := (continuous_const.prodMk continuous_id).continuousAt.eventually (hU.mem_nhds hMem)
    filter_upwards [hUInput] with w hw
    exact fderiv_normalVerticalJacobian_apply expMap y w b c (hReg.contDiffAt (hU.mem_nhds hw))
  have hJ := hN.contDiffAt_normalVerticalJacobian hy v hv
  have hDJ := (hJ.fderiv_right (m:=∞) (by simp)).differentiableAt (by simp)
  have hL := (hDJ.hasFDerivAt.clm_apply (hasFDerivAt_const b v)).clm_apply (hasFDerivAt_const c v)
  have hValue := congrArg (fun L => L a) hL.fderiv
  simp only [_root_.add_apply,ContinuousLinearMap.comp_apply,ContinuousLinearMap.flip_apply,
    zero_apply,map_zero,zero_add] at hValue
  rw [← hValue,hNear.fderiv_eq,hEval.fderiv]
  simp only [_root_.add_apply,ContinuousLinearMap.comp_apply,ContinuousLinearMap.flip_apply,
    ContinuousLinearMap.inr_apply,zero_apply,map_zero,zero_add]

/-- Uniform third vertical derivative, extracted from the full joint estimate. -/
theorem Background.normalVerticalJacobian_second_derivative_bound {Y Ω : Set X}
    (hY : IsOpen Y) (hΩ : IsOpen Ω) {K : ℝ} {m : ℕ} {M : Fin (m+1) → ℝ}
    {g g₁ g₂ : MetricField} {e : Frame} (h : Background Ω K M g g₁ g₂ e)
    (hK : 0 < K) (hm : 4 ≤ m) {expMap : X × X → X} {R : X → ℝ}
    (hN : NormalCoordinates Y Ω g expMap R) (hR : ContinuousOn R Y)
    {y : X} (hy : y ∈ Y) (v : X) (hv : metricPair g y v v < (R y)^2) (hv1 : ‖v‖ ≤ 1) :
    ‖fderiv ℝ (fderiv ℝ (normalVerticalJacobian expMap y)) v‖ ≤
      backgroundThirdNormalVariationBudget hm K M := by
  have hBudget : 0 ≤ backgroundThirdNormalVariationBudget hm K M := by
    unfold backgroundThirdNormalVariationBudget thirdNormalVariationBudget secondNormalVariationBudget
      backgroundThirdConnectionBudget thirdConnectionBudget backgroundSecondConnectionBudget
      secondConnectionBudget backgroundConnectionDerivativeBudget
    positivity
  have hBound := h.normal_exp_third_fderiv_bound hY hΩ hK hm hN hR hy v hv hv1
  apply ContinuousLinearMap.opNorm_le_bound _ hBudget
  intro a
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro b
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro c
  rw [hN.second_fderiv_normalVerticalJacobian_apply hy v a b c hv.le]
  let L := fderiv ℝ (fderiv ℝ (fderiv ℝ expMap)) (y,v)
  have hApply : ‖L ((0:X),a) ((0:X),b) ((0:X),c)‖ ≤
      ‖L‖*‖((0:X),a)‖*‖((0:X),b)‖*‖((0:X),c)‖ :=
    (ContinuousLinearMap.le_opNorm₂ (L ((0:X),a)) ((0:X),b) ((0:X),c)).trans
      (by gcongr; exact L.le_opNorm ((0:X),a))
  have hb := hApply.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hBound (norm_nonneg _))
      (norm_nonneg _)) (norm_nonneg _))
  simpa only [Prod.norm_mk,norm_zero,max_eq_right (norm_nonneg _)] using hb

end ShrinkingSpheres
