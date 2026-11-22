module

public import Proof.CalderonN.NormalJointThirdVariationBounds

import Mathlib.Tactic

/-! Adapted from the checked Proposition 5.3 release, Proof/NormalJointEndpointJets.lean. -/

public section

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1400000
set_option maxSynthPendingDepth 20
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter
open scoped ContDiff Topology
namespace CalderonN

variable {dim : ℕ} [NeZero dim]

lemma NormalCoordinates.joint_first_variation_position_eq {Y Ω : Set (X dim)} {g : (MetricField dim)}
    {expMap : (X dim) × (X dim) → (X dim)} {R : (X dim) → ℝ} (hN : NormalCoordinates Y Ω g expMap R)
    {y : (X dim)} (hy : y ∈ Y) (v : (X dim)) (h : (X dim) × (X dim)) (hv : v ∈ disk g y (R y)) :
    (firstParameterVariation (normalJointPhase expMap) h ((y,v),1)).1 = fderiv ℝ expMap (y,v) h := by
  have hPhase := hN.contDiffAt_jointPhase hy v 1 (by simpa only [one_smul] using hv)
  have hSlice : ContDiffAt ℝ ∞ (fun p => normalJointPhase expMap (p,1)) (y,v) :=
    hPhase.comp (y,v) (contDiffAt_id.prodMk contDiffAt_const)
  have hFst := (hSlice.differentiableAt (by simp)).hasFDerivAt.fst
  have hEq : (fun p => (normalJointPhase expMap (p,1)).1) = expMap := by
    funext p
    simp only [normalJointPhase,one_smul]
  calc
    _ = (fderiv ℝ (fun p => normalJointPhase expMap (p,1)) (y,v) h).1 := by
      rw [fderiv_base_slice_of_contDiffAt _ (y,v) h 1 hPhase]
      rfl
    _ = fderiv ℝ (fun p => (normalJointPhase expMap (p,1)).1) (y,v) h := by
      rw [hFst.fderiv]
      rfl
    _ = _ := by rw [hEq]

lemma NormalCoordinates.joint_second_variation_position_eq {Y Ω : Set (X dim)}
    (hY : IsOpen Y) (hΩ : IsOpen Ω) {K : ℝ} {g : (MetricField dim)} (hg : Elliptic Ω K g)
    {expMap : (X dim) × (X dim) → (X dim)} {R : (X dim) → ℝ} (hN : NormalCoordinates Y Ω g expMap R)
    {y : (X dim)} (hy : y ∈ Y) (hR : ContinuousAt R y) (v : (X dim)) (h k : (X dim) × (X dim))
    (hv : metricPair g y v v < (R y)^2) :
    (secondParameterVariation (normalJointPhase expMap) h k ((y,v),1)).1 =
      fderiv ℝ (fderiv ℝ expMap) (y,v) k h := by
  have hPhase := hN.contDiffAt_jointPhase hy v 1
    (by simpa only [one_smul] using (show v ∈ disk g y (R y) from hv.le))
  let J := firstParameterVariation (normalJointPhase expMap) h
  have hJ := contDiffAt_firstParameterVariation (normalJointPhase expMap) h ((y,v),1) hPhase
  have hSlice : ContDiffAt ℝ ∞ (fun p => J (p,1)) (y,v) :=
    hJ.comp (y,v) (contDiffAt_id.prodMk contDiffAt_const)
  have hFst := (hSlice.differentiableAt (by simp)).hasFDerivAt.fst
  have hNear : (fun p => (J (p,1)).1) =ᶠ[𝓝 (y,v)] (fun p => fderiv ℝ expMap p h) := by
    filter_upwards [hN.eventually_joint_disk hY hΩ hg hy hR v hv] with p hp
    exact hN.joint_first_variation_position_eq hp.1 p.2 h hp.2
  obtain ⟨U,hU,hTube,hReg⟩ := hN.1
  have hE : ContDiffAt ℝ ∞ expMap (y,v) := hReg.contDiffAt (hU.mem_nhds (hTube ⟨hy,hv.le⟩))
  calc
    _ = (fderiv ℝ (fun p => J (p,1)) (y,v) k).1 := by
      rw [fderiv_base_slice_of_contDiffAt J (y,v) k 1 hJ]
      rfl
    _ = fderiv ℝ (fun p => (J (p,1)).1) (y,v) k := by
      rw [hFst.fderiv]
      rfl
    _ = fderiv ℝ (fun p => fderiv ℝ expMap p h) (y,v) k :=
      congrArg (fun T : ((X dim) × (X dim)) →L[ℝ] (X dim) => T k) hNear.fderiv_eq
    _ = _ := fderiv_apply_const_of_contDiffAt expMap (y,v) h k hE

lemma NormalCoordinates.joint_third_variation_position_eq {Y Ω : Set (X dim)}
    (hY : IsOpen Y) (hΩ : IsOpen Ω) {K : ℝ} {g : (MetricField dim)} (hg : Elliptic Ω K g)
    {expMap : (X dim) × (X dim) → (X dim)} {R : (X dim) → ℝ} (hN : NormalCoordinates Y Ω g expMap R)
    (hR : ContinuousOn R Y) {y : (X dim)} (hy : y ∈ Y) (v : (X dim)) (h k l : (X dim) × (X dim))
    (hv : metricPair g y v v < (R y)^2) :
    (thirdParameterVariation (normalJointPhase expMap) h k l ((y,v),1)).1 =
      fderiv ℝ (fderiv ℝ (fderiv ℝ expMap)) (y,v) l k h := by
  have hPhase := hN.contDiffAt_jointPhase hy v 1
    (by simpa only [one_smul] using (show v ∈ disk g y (R y) from hv.le))
  let S := secondParameterVariation (normalJointPhase expMap) h k
  have hS := contDiffAt_secondParameterVariation (normalJointPhase expMap) h k ((y,v),1) hPhase
  have hSlice : ContDiffAt ℝ ∞ (fun p => S (p,1)) (y,v) :=
    hS.comp (y,v) (contDiffAt_id.prodMk contDiffAt_const)
  have hFst := (hSlice.differentiableAt (by simp)).hasFDerivAt.fst
  have hNear : (fun p => (S (p,1)).1) =ᶠ[𝓝 (y,v)]
      (fun p => fderiv ℝ (fderiv ℝ expMap) p k h) := by
    filter_upwards [hN.eventually_joint_strict_disk hY hΩ hg hy
      (hR.continuousAt (hY.mem_nhds hy)) v hv] with p hp
    exact hN.joint_second_variation_position_eq hY hΩ hg hp.1
      (hR.continuousAt (hY.mem_nhds hp.1)) p.2 h k hp.2
  obtain ⟨U,hU,hTube,hReg⟩ := hN.1
  have hE : ContDiffAt ℝ ∞ expMap (y,v) := hReg.contDiffAt (hU.mem_nhds (hTube ⟨hy,hv.le⟩))
  have hDD := ((hE.fderiv_right (m:=∞) (by simp)).fderiv_right (m:=∞) (by simp)).differentiableAt (by simp)
  have hEval := (hDD.hasFDerivAt.clm_apply (hasFDerivAt_const k (y,v))).clm_apply (hasFDerivAt_const h (y,v))
  have hValue := congrArg (fun L => L l) hEval.fderiv
  simp only [_root_.add_apply,ContinuousLinearMap.comp_apply,ContinuousLinearMap.flip_apply,
    zero_apply,map_zero,zero_add] at hValue
  calc
    _ = (fderiv ℝ (fun p => S (p,1)) (y,v) l).1 := by
      rw [fderiv_base_slice_of_contDiffAt S (y,v) l 1 hS]
      rfl
    _ = fderiv ℝ (fun p => (S (p,1)).1) (y,v) l := by
      rw [hFst.fderiv]
      rfl
    _ = fderiv ℝ (fun p => fderiv ℝ (fderiv ℝ expMap) p k h) (y,v) l :=
      congrArg (fun T : ((X dim) × (X dim)) →L[ℝ] (X dim) => T l) hNear.fderiv_eq
    _ = _ := hValue

/-- Uniform full third Frechet derivative of the actual exponential map,
    including every mixed center/velocity direction. -/
theorem Background.normal_exp_third_fderiv_bound {Y Ω : Set (X dim)} (hY : IsOpen Y) (hΩ : IsOpen Ω)
    {K : ℝ} {m : ℕ} {M : Fin (m+1) → ℝ} {g g₁ g₂ : (MetricField dim)} {e : Frame dim}
    (h : Background Ω K M g g₁ g₂ e) (hK : 0 < K) (hm : 4 ≤ m)
    {expMap : (X dim) × (X dim) → (X dim)} {R : (X dim) → ℝ} (hN : NormalCoordinates Y Ω g expMap R)
    (hR : ContinuousOn R Y) {y : (X dim)} (hy : y ∈ Y) (v : (X dim))
    (hv : metricPair g y v v < (R y)^2) (hv1 : ‖v‖ ≤ 1) :
    ‖fderiv ℝ (fderiv ℝ (fderiv ℝ expMap)) (y,v)‖ ≤ backgroundThirdNormalVariationBudget dim hm K M := by
  have hBudget : 0 ≤ backgroundThirdNormalVariationBudget dim hm K M := by
    unfold backgroundThirdNormalVariationBudget thirdNormalVariationBudget secondNormalVariationBudget
      backgroundThirdConnectionBudget thirdConnectionBudget backgroundSecondConnectionBudget
      secondConnectionBudget backgroundConnectionDerivativeBudget
    positivity
  apply ContinuousLinearMap.opNorm_le_bound _ hBudget
  intro a
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro b
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro c
  have hb := h.normal_joint_third_variation_bound hY hΩ hK hm hN hR hy v c b a hv hv1
    (show (1:ℝ) ∈ Icc (0:ℝ) 1 by constructor <;> norm_num)
  have hh := (norm_fst_le (thirdParameterVariation (normalJointPhase expMap) c b a ((y,v),1))).trans hb
  rw [hN.joint_third_variation_position_eq hY hΩ h.1 hR hy v c b a hv] at hh
  exact hh.trans_eq (by ring)

end CalderonN
