module

public import Proof.CalderonN.UniformFourthNormalVariation
public import Proof.CalderonN.NormalJointEndpointJets

import Mathlib.Tactic

/-! Adapted from the checked Proposition 5.3 release, Proof/NormalJointFourthEndpointJet.lean. -/

public section

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter
open scoped ContDiff Topology
namespace CalderonN

variable {dim : ℕ} [NeZero dim]

lemma NormalCoordinates.joint_fourth_variation_position_eq {Y Ω : Set (X dim)}
    (hY : IsOpen Y) (hΩ : IsOpen Ω) {K : ℝ} {g : (MetricField dim)} (hg : Elliptic Ω K g)
    {expMap : (X dim) × (X dim) → (X dim)} {R : (X dim) → ℝ} (hN : NormalCoordinates Y Ω g expMap R)
    (hR : ContinuousOn R Y) {y : (X dim)} (hy : y ∈ Y) (v : (X dim)) (h k l m : (X dim) × (X dim))
    (hv : metricPair g y v v < (R y)^2) :
    (fourthParameterVariation (normalJointPhase expMap) h k l m ((y,v),1)).1 =
      fderiv ℝ (fderiv ℝ (fderiv ℝ (fderiv ℝ expMap))) (y,v) m l k h := by
  have hPhase := hN.contDiffAt_jointPhase hy v 1
    (by simpa only [one_smul] using (show v ∈ disk g y (R y) from hv.le))
  let S := thirdParameterVariation (normalJointPhase expMap) h k l
  have hS := contDiffAt_thirdParameterVariation (normalJointPhase expMap) h k l ((y,v),1) hPhase
  have hSlice : ContDiffAt ℝ ∞ (fun p => S (p,1)) (y,v) :=
    hS.comp (y,v) (contDiffAt_id.prodMk contDiffAt_const)
  have hFst := (hSlice.differentiableAt (by simp)).hasFDerivAt.fst
  have hNear : (fun p => (S (p,1)).1) =ᶠ[𝓝 (y,v)]
      (fun p => fderiv ℝ (fderiv ℝ (fderiv ℝ expMap)) p l k h) := by
    filter_upwards [hN.eventually_joint_strict_disk hY hΩ hg hy
      (hR.continuousAt (hY.mem_nhds hy)) v hv] with p hp
    exact hN.joint_third_variation_position_eq hY hΩ hg hR hp.1 p.2 h k l hp.2
  obtain ⟨U,hU,hTube,hReg⟩ := hN.1
  have hE : ContDiffAt ℝ ∞ expMap (y,v) := hReg.contDiffAt (hU.mem_nhds (hTube ⟨hy,hv.le⟩))
  have hDDD := (((hE.fderiv_right (m:=∞) (by simp)).fderiv_right (m:=∞) (by simp)).fderiv_right (m:=∞) (by simp)).differentiableAt (by simp)
  have hEval := ((hDDD.hasFDerivAt.clm_apply (hasFDerivAt_const l (y,v))).clm_apply (hasFDerivAt_const k (y,v))).clm_apply (hasFDerivAt_const h (y,v))
  have hValue := congrArg (fun L => L m) hEval.fderiv
  simp only [_root_.add_apply,ContinuousLinearMap.comp_apply,ContinuousLinearMap.flip_apply,
    zero_apply,map_zero,zero_add] at hValue
  calc
    _ = (fderiv ℝ (fun p => S (p,1)) (y,v) m).1 := by
      rw [fderiv_base_slice_of_contDiffAt S (y,v) m 1 hS]
      rfl
    _ = fderiv ℝ (fun p => (S (p,1)).1) (y,v) m := by
      rw [hFst.fderiv]
      rfl
    _ = fderiv ℝ (fun p => fderiv ℝ (fderiv ℝ (fderiv ℝ expMap)) p l k h) (y,v) m :=
      congrArg (fun T : ((X dim) × (X dim)) →L[ℝ] (X dim) => T m) hNear.fderiv_eq
    _ = _ := hValue

/-- Uniform full fourth Frechet derivative of the actual exponential map,
    including every mixed center/velocity direction. -/
theorem Background.normal_exp_fourth_fderiv_bound {Y Ω : Set (X dim)} (hY : IsOpen Y) (hΩ : IsOpen Ω)
    {K : ℝ} {m : ℕ} {M : Fin (m+1) → ℝ} {g g₁ g₂ : (MetricField dim)} {e : Frame dim}
    (h : Background Ω K M g g₁ g₂ e) (hK : 0 < K) (hm : 5 ≤ m)
    {expMap : (X dim) × (X dim) → (X dim)} {R : (X dim) → ℝ} (hN : NormalCoordinates Y Ω g expMap R)
    (hR : ContinuousOn R Y) {y : (X dim)} (hy : y ∈ Y) (v : (X dim))
    (hv : metricPair g y v v < (R y)^2) (hv1 : ‖v‖ ≤ 1) :
    ‖fderiv ℝ (fderiv ℝ (fderiv ℝ (fderiv ℝ expMap))) (y,v)‖ ≤ backgroundFourthNormalVariationBudget dim hm K M := by
  have hBudget : 0 ≤ backgroundFourthNormalVariationBudget dim hm K M := by
    unfold backgroundFourthNormalVariationBudget fourthNormalVariationBudget fourthVariationForcingBudget
      thirdNormalVariationBudget secondNormalVariationBudget
      backgroundFourthConnectionBudget fourthConnectionBudget fourthChristoffelBudget fourthInverseMetricBudget
      backgroundThirdConnectionBudget thirdConnectionBudget backgroundSecondConnectionBudget
      secondConnectionBudget backgroundConnectionDerivativeBudget
    positivity
  apply ContinuousLinearMap.opNorm_le_bound _ hBudget
  intro a
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro b
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro c
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro d
  have hb := h.normal_joint_fourth_variation_bound hY hΩ hK hm hN hR hy v d c b a hv hv1
    (show (1:ℝ) ∈ Icc (0:ℝ) 1 by constructor <;> norm_num)
  have hh := (norm_fst_le (fourthParameterVariation (normalJointPhase expMap) d c b a ((y,v),1))).trans hb
  rw [hN.joint_fourth_variation_position_eq hY hΩ h.1 hR hy v d c b a hv] at hh
  exact hh.trans_eq (by ring)

end CalderonN
