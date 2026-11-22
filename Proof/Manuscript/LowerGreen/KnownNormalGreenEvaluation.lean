module

public import Proof.CalderonN.LocalNormalGreenFlux
public import Proof.CalderonN.LocalChartExtension

import Proof.CalderonN.NormalInverse
import Proof.CalderonN.CrossProductWeak
import Mathlib.Analysis.Normed.Module.Ball.Pointwise
import Mathlib.Tactic

public section

noncomputable section

open Set Filter Metric CalderonN
open scoped ContDiff Topology

namespace CalderonPaper.LowerGreen

variable {n : ℕ} [NeZero n] [Nontrivial (Fin n)]

/- The compact radius-room argument from LocalNormalGreenFlux.lean is
used here for evaluation on a known Green slice. -/
private theorem exists_larger_normalBall_inside
    {U : Set (X n)} (hU : IsOpen U) {γ : (MetricField n)} {E : (X n) × (X n) → (X n)} (hE : Continuous E)
    {e : (Frame n)} {y : (X n)}
    (he : ∀ i j, metricPair γ y (e y i) (e y j) = if i = j then 1 else 0)
    {r ρ : ℝ} (hr : 0 < r) (hR : r < ρ)
    (hCover : closedBallImage γ E (fun _ => r) y ⊆ U) :
    ∃ s, r < s ∧ s < ρ ∧ closedBallImage γ E (fun _ => s) y ⊆ U := by
  let F : (X n) → (X n) := fun v => E (y,frameVector e y v)
  let P := F ⁻¹' U
  have hF : Continuous F := hE.comp (continuous_const.prodMk (continuous_frameVector e y))
  have hP : IsOpen P := hU.preimage hF
  have hC : closedBall (0 : (X n)) r ⊆ P := by
    rw [closedBallImage_eq_frameImage γ E e y he hr.le] at hCover
    exact fun x hx => hCover (mem_image_of_mem F hx)
  obtain ⟨b,hb,hs⟩ := (isCompact_closedBall (0 : (X n)) r).exists_thickening_subset_open hP hC
  rw [thickening_closedBall hb hr.le] at hs
  let s := r+min (b/2) ((ρ-r)/2)
  have hs₀ : r < s := lt_add_of_pos_right _ (lt_min (by positivity) (by linarith))
  have hcap : s < ρ := by
    have h := min_le_right (b/2) ((ρ-r)/2)
    dsimp [s]
    linarith
  have hbs : s < b+r := by
    have h := min_le_left (b/2) ((ρ-r)/2)
    dsimp [s]
    linarith
  refine ⟨s,hs₀,hcap,?_⟩
  rw [closedBallImage_eq_frameImage γ E e y he (hr.trans hs₀).le]
  rintro x ⟨z,hz,rfl⟩
  exact hs (closedBall_subset_ball hbs hz)

set_option maxHeartbeats 1800000 in
/-- Evaluation of arbitrary locally harmonic data from a known Green
slice, with the cutoff chosen in the actual harmonic neighborhood. -/
theorem knownNormalGreenFlux_eq_value
    {Y Ω : Set (X n)} (hY : IsOpen Y) (hΩ : IsOpen Ω)
    {γ g₁ g₂ : MetricField n} (hγ : SmoothMetric univ γ) (hg : SmoothMetric Ω g₁)
    {ρ : ℝ} {E : X n × X n → X n} (hE : ContDiff ℝ ∞ E)
    (hN : NormalCoordinates Y Ω γ E (fun _ => ρ))
    {O : Set (X n × X n)} (hO : IsOpen O) {G K : X n × X n → ℝ}
    (hG : ProductSolutionOn g₁ g₂ O G) (hK : GreenGerm Ω g₁ K)
    {e : Frame n} (he : ∀ y ∈ Y, ∀ i j, metricPair γ y (e y i) (e y j) = if i=j then 1 else 0)
    (hec : ∀ i, ContinuousOn (fun y => e y i) Y) {r : X n → ℝ}
    (hrc : ContinuousOn r Y) (hr : ∀ y ∈ Y, 0 < r y ∧ r y < ρ)
    {y₀ : X n} (hy₀ : y₀ ∈ Y)
    (hSphere : ∀ w : ↥(standardSphere n), (E (y₀,r y₀ • frameVector e y₀ w),y₀) ∈ O)
    (hKnown : ∀ x, (x,y₀) ∈ normalPairDomain Y γ ρ E → x ≠ y₀ → G (x,y₀) = K (x,y₀))
    {U : Set (X n)} (hU : IsOpen U) (hCover : closedBallImage γ E r y₀ ⊆ U) {u : X n → ℝ}
    (hu : Harmonic U g₁ u) :
    normalSphereGreenFlux g₁ E e r G y₀ u = u y₀ := by
  let T := U ∩ Ω
  have hT : IsOpen T := hU.inter hΩ
  have hCover₀ : closedBallImage γ E r y₀ ⊆ T := by
    intro z hz
    refine ⟨hCover hz,?_⟩
    obtain ⟨v,hv,rfl⟩ := hz
    have hv' : v ∈ disk γ y₀ ρ := hv.trans
      (pow_le_pow_left₀ (hr y₀ hy₀).1.le (hr y₀ hy₀).2.le 2)
    exact ((hN.2 y₀ hy₀).2.2 v hv').1
  obtain ⟨s,hs,hcap,hbig⟩ := exists_larger_normalBall_inside hT hE.continuous (he y₀ hy₀)
    (hr y₀ hy₀).1 (hr y₀ hy₀).2 hCover₀
  have hs₀ : 0 < s := (hr y₀ hy₀).1.trans hs
  have hEv := eventually_closedBallImage_subset hE.continuous hT (hY.mem_nhds hy₀) he
    (fun i => (hec i).continuousAt (hY.mem_nhds hy₀)) (r := fun _ => s) continuousAt_const hs₀ hbig
  have hRad : ∀ᶠ y in 𝓝 y₀, r y < s :=
    (hrc.continuousAt (hY.mem_nhds hy₀)).eventually (gt_mem_nhds hs)
  have hNear : {y | closedBallImage γ E (fun _ => s) y ⊆ T} ∩ {y | r y < s} ∩ Y ∈ 𝓝 y₀ :=
    inter_mem (inter_mem hEv hRad) (hY.mem_nhds hy₀)
  obtain ⟨V,hV,hVo,hyV⟩ := _root_.mem_nhds_iff.mp hNear
  have hVY : V ⊆ Y := fun y hy => (hV hy).2
  have hrV (y : X n) (hy : y ∈ V) : 0 < r y ∧ r y < s := ⟨(hr y (hVY hy)).1,(hV hy).1.2⟩
  have hDisk (y v : X n) (hv : v ∈ disk γ y s) : v ∈ disk γ y ρ :=
    hv.trans (pow_le_pow_left₀ hs₀.le hcap.le 2)
  have hNV : NormalCoordinates V T γ E (fun _ => s) := by
    refine ⟨⟨univ,isOpen_univ,subset_univ _,hE.contDiffOn⟩,fun y hy => ?_⟩
    obtain ⟨_,hInj,hYdata⟩ := hN.2 y (hVY hy)
    refine ⟨hs₀,hInj.mono (fun v hv => hDisk y v hv),fun v hv => ?_⟩
    exact ⟨(hV hy).1.1 ⟨v,hv,rfl⟩,(hYdata v (hDisk y v hv)).2⟩
  obtain ⟨hP,hPT,L,hL,hExact,hInv⟩ :=
    exists_normal_inverse_velocity hVo (smoothMetric_restrict hγ (subset_univ V)) hNV
  have huT : Harmonic T g₁ u := ⟨hu.1.mono inter_subset_left,fun z hz => hu.2 z hz.1⟩
  obtain ⟨η,φ,hφ⟩ := exists_eventually_normalGreenCutoff hVo hT hγ hE.continuous hP hPT hL.continuousOn
    hExact hInv hO hyV (fun y hy => he y (hVY hy))
    (fun i => (hec i).continuousAt (hY.mem_nhds hy₀)) (hrc.continuousAt (hY.mem_nhds hy₀))
    (hrV y₀ hyV).1 (hrV y₀ hyV).2 hSphere huT.1
  have hTest := mem_of_mem_nhds hφ
  have hCenter : E (y₀,(0 : X n)) = y₀ := by
    have h0 : (0 : X n) ∈ disk γ y₀ s := by simp [disk,metricPair,sq_nonneg]
    simpa only [zero_smul] using ((hNV.2 y₀ hyV).2.2 0 h0).2.2.1
  have hGerm := GreenGerm.restrict_congr_metric hΩ hT inter_subset_right hg (fun _ _ => rfl) hK
  have hEq (x : X n) (hx : (x,y₀) ∈ normalPairDomain V γ s E) (hne : x ≠ y₀) :
      G (x,y₀) = K (x,y₀) := by
    apply hKnown x _ hne
    obtain ⟨q,hq,hEq⟩ := hx
    refine ⟨q,⟨hVY hq.1,?_⟩,hEq⟩
    exact hq.2.trans_le (pow_le_pow_left₀ hs₀.le hcap.le 2)
  exact (hTest.pairing_eq_normalSphereGreenFlux hT (smoothMetric_restrict hg inter_subset_right)
    hE hNV hExact hInv hO hG hyV (he y₀ hy₀) huT).symm.trans
      (hTest.pairing_eq_value hT hPT hExact hInv hyV hCenter huT hGerm hEq)

end CalderonPaper.LowerGreen

end
