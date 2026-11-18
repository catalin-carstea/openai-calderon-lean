import Proof.JointNormalMetricJetEnvelope
import Proof.NormalJointFourthEndpointJet
import Proof.NormalJointSecondEndpointBound
import Proof.MetricDensityBounds

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set
open scoped ContDiff
namespace ShrinkingSpheres

def backgroundExpJetEnvelope {m : ℕ} (hm : 5 ≤ m) (K : ℝ) (M : Fin (m+1) → ℝ) : ℝ :=
  1+Real.exp (normalVariationBudget (by omega) K M)+
    backgroundSecondNormalVariationBudget (by omega) K M+
    backgroundThirdNormalVariationBudget (by omega) K M+backgroundFourthNormalVariationBudget hm K M

lemma backgroundExpJetEnvelope_ge_one {m : ℕ} (hm : 5 ≤ m) {K : ℝ} (hK : 0 ≤ K)
    (M : Fin (m+1) → ℝ) : 1 ≤ backgroundExpJetEnvelope hm K M := by
  have hS : 0 ≤ backgroundSecondNormalVariationBudget (show 3 ≤ m by omega) K M := by
    unfold backgroundSecondNormalVariationBudget secondNormalVariationBudget
      backgroundSecondConnectionBudget secondConnectionBudget backgroundConnectionDerivativeBudget
    positivity
  have hT : 0 ≤ backgroundThirdNormalVariationBudget (show 4 ≤ m by omega) K M := by
    unfold backgroundThirdNormalVariationBudget thirdNormalVariationBudget secondNormalVariationBudget
      backgroundThirdConnectionBudget thirdConnectionBudget backgroundSecondConnectionBudget
      secondConnectionBudget backgroundConnectionDerivativeBudget
    positivity
  have hQ : 0 ≤ backgroundFourthNormalVariationBudget hm K M := by
    unfold backgroundFourthNormalVariationBudget fourthNormalVariationBudget fourthVariationForcingBudget
      thirdNormalVariationBudget secondNormalVariationBudget backgroundFourthConnectionBudget
      fourthConnectionBudget fourthChristoffelBudget fourthInverseMetricBudget
      backgroundThirdConnectionBudget thirdConnectionBudget backgroundSecondConnectionBudget
      secondConnectionBudget backgroundConnectionDerivativeBudget
    positivity
  dsimp only [backgroundExpJetEnvelope]
  linarith [Real.exp_pos (normalVariationBudget (show 2 ≤ m by omega) K M)]

theorem Background.normal_exp_first_fderiv_bound {Y Ω : Set X} (hY : IsOpen Y) (hΩ : IsOpen Ω)
    {K : ℝ} {m : ℕ} {M : Fin (m+1) → ℝ} {g g₁ g₂ : MetricField} {e : Frame}
    (h : Background Ω K M g g₁ g₂ e) (hK : 0 < K) (hm : 2 ≤ m)
    {expMap : X × X → X} {R : X → ℝ} (hN : NormalCoordinates Y Ω g expMap R)
    (hR : ContinuousOn R Y) {y : X} (hy : y ∈ Y) (v : X)
    (hv : metricPair g y v v < (R y)^2) (hv1 : ‖v‖ ≤ 1) :
    ‖fderiv ℝ expMap (y,v)‖ ≤ Real.exp (normalVariationBudget hm K M) := by
  apply ContinuousLinearMap.opNorm_le_bound _ (Real.exp_pos _).le
  intro a
  have hb := hN.joint_variation_bound hY hΩ h.1 hK
    (show 0 ≤ 243*K*|M ⟨1,by omega⟩| by positivity)
    (show 0 ≤ backgroundConnectionDerivativeBudget hm K M by unfold backgroundConnectionDerivativeBudget;positivity)
    (fun x hx => h.connection_budget hK (by omega) hx)
    (fun x hx => h.connection_derivative_budget hΩ hK hm hx) hy
    (hR.continuousAt (hY.mem_nhds hy)) v a.1 a.2 hv hv1
    (show (1:ℝ) ∈ Icc (0:ℝ) 1 by constructor <;> norm_num)
  have hh := (norm_fst_le (normalJointVariation expMap y v a.1 a.2 1)).trans hb
  change ‖(firstParameterVariation (normalJointPhase expMap) a ((y,v),1)).1‖ ≤ _ at hh
  rw [hN.joint_first_variation_position_eq hy v a hv.le] at hh
  simpa only [normalVariationBudget,mul_one,Prod.mk.eta] using hh.trans_eq (mul_comm _ _)

/-- A single envelope controls every nonzero joint exponential jet through four. -/
theorem Background.normal_exp_jet_envelope {Y Ω : Set X} (hY : IsOpen Y) (hΩ : IsOpen Ω)
    {K : ℝ} {m : ℕ} {M : Fin (m+1) → ℝ} {g g₁ g₂ : MetricField} {e : Frame}
    (h : Background Ω K M g g₁ g₂ e) (hK : 0 < K) (hm : 5 ≤ m)
    {expMap : X × X → X} {R : X → ℝ} (hN : NormalCoordinates Y Ω g expMap R)
    (hR : ContinuousOn R Y) {y : X} (hy : y ∈ Y) (v : X)
    (hv : metricPair g y v v < (R y)^2) (hv1 : ‖v‖ ≤ 1) :
    ∀ n,1 ≤ n → n ≤ 4 → ‖iteratedFDeriv ℝ n expMap (y,v)‖ ≤ backgroundExpJetEnvelope hm K M := by
  let A := Real.exp (normalVariationBudget (show 2 ≤ m by omega) K M)
  let S := backgroundSecondNormalVariationBudget (show 3 ≤ m by omega) K M
  let T := backgroundThirdNormalVariationBudget (show 4 ≤ m by omega) K M
  let Q := backgroundFourthNormalVariationBudget hm K M
  have hA : 0 ≤ A := (Real.exp_pos _).le
  have hS : 0 ≤ S := by
    dsimp [S,backgroundSecondNormalVariationBudget,secondNormalVariationBudget,
      backgroundSecondConnectionBudget,secondConnectionBudget,backgroundConnectionDerivativeBudget];positivity
  have hT : 0 ≤ T := by
    dsimp [T,backgroundThirdNormalVariationBudget,thirdNormalVariationBudget,secondNormalVariationBudget,
      backgroundThirdConnectionBudget,thirdConnectionBudget,backgroundSecondConnectionBudget,
      secondConnectionBudget,backgroundConnectionDerivativeBudget];positivity
  have hQ : 0 ≤ Q := by
    dsimp [Q,backgroundFourthNormalVariationBudget,fourthNormalVariationBudget,fourthVariationForcingBudget,
      thirdNormalVariationBudget,secondNormalVariationBudget,backgroundFourthConnectionBudget,
      fourthConnectionBudget,fourthChristoffelBudget,fourthInverseMetricBudget,
      backgroundThirdConnectionBudget,thirdConnectionBudget,backgroundSecondConnectionBudget,
      secondConnectionBudget,backgroundConnectionDerivativeBudget];positivity
  have hb1 := h.normal_exp_first_fderiv_bound hY hΩ hK (show 2 ≤ m by omega) hN hR hy v hv hv1
  have hb2 := h.normal_exp_second_fderiv_bound hY hΩ hK (show 3 ≤ m by omega) hN hy
    (hR.continuousAt (hY.mem_nhds hy)) v hv hv1
  have hb3 := h.normal_exp_third_fderiv_bound hY hΩ hK (show 4 ≤ m by omega) hN hR hy v hv hv1
  have hb4 := h.normal_exp_fourth_fderiv_bound hY hΩ hK hm hN hR hy v hv hv1
  intro n hn hn4
  change ‖iteratedFDeriv ℝ n expMap (y,v)‖ ≤ 1+A+S+T+Q
  change _ ≤ A at hb1
  change _ ≤ S at hb2
  change _ ≤ T at hb3
  change _ ≤ Q at hb4
  interval_cases n
  · rw [norm_iteratedFDeriv_one];linarith only [hb1,hA,hS,hT,hQ]
  · rw [← norm_iteratedFDeriv_fderiv (n:=1),norm_iteratedFDeriv_one];linarith only [hb2,hA,hS,hT,hQ]
  · rw [← norm_iteratedFDeriv_fderiv (n:=2),← norm_iteratedFDeriv_fderiv (n:=1),norm_iteratedFDeriv_one]
    linarith only [hb3,hA,hS,hT,hQ]
  · rw [norm_iteratedFDeriv_four_eq_nested];linarith only [hb4,hA,hS,hT,hQ]

def backgroundJointNormalMetricJetBudget {m : ℕ} (hm : 5 ≤ m) (K : ℝ) (M : Fin (m+1) → ℝ) : ℝ :=
  3456*(K+|M ⟨1,by omega⟩|+|M ⟨2,by omega⟩|+|M ⟨3,by omega⟩|)*(backgroundExpJetEnvelope hm K M)^5

/-- Joint tensor jets through order three are uniform for the actual admitted
    map and either metric, before any derivatives of a chosen frame. -/
theorem Background.joint_normal_metric_jet_bound {Y Ω : Set X} (hY : IsOpen Y) (hΩ : IsOpen Ω)
    {K : ℝ} {m : ℕ} {M : Fin (m+1) → ℝ} {g g₁ g₂ : MetricField} {e : Frame}
    (h : Background Ω K M g g₁ g₂ e) (hK : 0 < K) (hm : 5 ≤ m)
    {expMap : X × X → X} {R : X → ℝ} (hN : NormalCoordinates Y Ω g expMap R)
    (hR : ContinuousOn R Y) {y : X} (hy : y ∈ Y) (v u w : X)
    (hv : metricPair g y v v < (R y)^2) (hv1 : ‖v‖ ≤ 1)
    (g' : MetricField) (hmem : g' ∈ ({g,g₁}:Set MetricField)) :
    ∀ n,n ≤ 3 → ‖iteratedFDeriv ℝ n (jointNormalMetricPair g' expMap u w) (y,v)‖ ≤
      backgroundJointNormalMetricJetBudget hm K M*‖u‖*‖w‖ := by
  have hg' : Elliptic Ω K g' := by
    simp only [mem_insert_iff,mem_singleton_iff] at hmem
    rcases hmem with rfl | rfl
    · exact h.1
    · exact h.2.1
  have hx : expMap (y,v) ∈ Ω := by
    simpa only [one_smul] using hN.path_image hy v hv.le
      (show (1:ℝ) ∈ Icc (0:ℝ) 1 by constructor <;> norm_num)
  obtain ⟨U,hU,hTube,hReg⟩ := hN.1
  have hE : ContDiffAt ℝ ∞ expMap (y,v) := hReg.contDiffAt (hU.mem_nhds (hTube ⟨hy,hv.le⟩))
  let C := K+|M ⟨1,by omega⟩|+|M ⟨2,by omega⟩|+|M ⟨3,by omega⟩|
  have hC : 0 ≤ C := by dsimp [C];linarith [abs_nonneg (M ⟨1,by omega⟩),abs_nonneg (M ⟨2,by omega⟩),abs_nonneg (M ⟨3,by omega⟩)]
  apply norm_jointNormalMetricPair_third_jet_envelope g' expMap (y,v) u w hE
    (fun i j => (hg'.1 i j).contDiffAt (hΩ.mem_nhds hx)) C (backgroundExpJetEnvelope hm K M) hC
    (backgroundExpJetEnvelope_ge_one hm hK.le M) ?_ (h.normal_exp_jet_envelope hY hΩ hK hm hN hR hy v hv hv1)
  intro i j n hn
  by_cases hn0 : n = 0
  · subst n
    simp only [norm_iteratedFDeriv_zero,Real.norm_eq_abs]
    exact (hg'.entry_abs_bound hK hx i j).trans (by dsimp [C];linarith [abs_nonneg (M ⟨1,by omega⟩),abs_nonneg (M ⟨2,by omega⟩),abs_nonneg (M ⟨3,by omega⟩)])
  · have hb := h.2.2.2.2.1 g' hmem ⟨n,by omega⟩ i j _ hx
    have hb' := hb.trans (le_abs_self _)
    have hOne : |M ⟨1,by omega⟩| ≤ C := by dsimp [C];linarith [abs_nonneg (M ⟨1,by omega⟩),abs_nonneg (M ⟨2,by omega⟩),abs_nonneg (M ⟨3,by omega⟩)]
    have hTwo : |M ⟨2,by omega⟩| ≤ C := by dsimp [C];linarith [abs_nonneg (M ⟨1,by omega⟩),abs_nonneg (M ⟨2,by omega⟩),abs_nonneg (M ⟨3,by omega⟩)]
    have hThree : |M ⟨3,by omega⟩| ≤ C := by dsimp [C];linarith [abs_nonneg (M ⟨1,by omega⟩),abs_nonneg (M ⟨2,by omega⟩),abs_nonneg (M ⟨3,by omega⟩)]
    interval_cases n <;> first | contradiction | exact hb'.trans hOne | exact hb'.trans hTwo | exact hb'.trans hThree

end ShrinkingSpheres
