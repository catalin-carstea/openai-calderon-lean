module

public import Proof.CalderonN.NormalGreenFlux
public import Proof.CalderonN.NormalGreenTransfer

import Proof.CalderonN.CrossProductWeak
import Proof.CalderonN.GreenWeak
import Mathlib.Analysis.Normed.Module.Ball.Pointwise
import Mathlib.Tactic

/-! Adapted from `LocalNormalGreenFlux` in the checked Theorem 3.1 release. -/

public section

set_option maxHeartbeats 2400000

noncomputable section
open Set Filter Metric
open scoped ContDiff Topology

namespace CalderonN

variable {dim : ℕ} [NeZero dim] [Nontrivial (Fin dim)]

private theorem exists_larger_normalBall_inside
    {U : Set (X dim)} (hU : IsOpen U) {γ : (MetricField dim)} {E : (X dim) × (X dim) → (X dim)} (hE : Continuous E)
    {e : (Frame dim)} {y : (X dim)}
    (he : ∀ i j, metricPair γ y (e y i) (e y j) = if i = j then 1 else 0)
    {r ρ : ℝ} (hr : 0 < r) (hR : r < ρ)
    (hCover : closedBallImage γ E (fun _ => r) y ⊆ U) :
    ∃ s, r < s ∧ s < ρ ∧ closedBallImage γ E (fun _ => s) y ⊆ U := by
  let F : (X dim) → (X dim) := fun v => E (y,frameVector e y v)
  let P := F ⁻¹' U
  have hF : Continuous F := hE.comp (continuous_const.prodMk (continuous_frameVector e y))
  have hP : IsOpen P := hU.preimage hF
  have hC : closedBall (0 : (X dim)) r ⊆ P := by
    rw [closedBallImage_eq_frameImage γ E e y he hr.le] at hCover
    exact fun x hx => hCover (mem_image_of_mem F hx)
  obtain ⟨b,hb,hs⟩ := (isCompact_closedBall (0 : (X dim)) r).exists_thickening_subset_open hP hC
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

set_option maxHeartbeats 960000 in
/-- Local harmonicity of the literal first-metric sphere flux. The
test need only be harmonic near the original center's closed ball. -/
theorem exists_harmonic_normalSphereGreenFlux_near
    {Y Ω : Set (X dim)} (hY : IsOpen Y)
    {γ g₁ g₂ : (MetricField dim)} (hγ : SmoothMetric univ γ) (hg₁ : SmoothMetric univ g₁)
    {ρ : ℝ} {E : (X dim) × (X dim) → (X dim)} (hE : ContDiff ℝ ∞ E)
    (hN : NormalCoordinates Y Ω γ E (fun _ => ρ))
    {O : Set ((X dim) × (X dim))} (hO : IsOpen O)
    {G : (X dim) × (X dim) → ℝ} (hG : ProductSolutionOn g₁ g₂ O G)
    {e : (Frame dim)} (he : ∀ y ∈ Y, ∀ i j, metricPair γ y (e y i) (e y j) = if i = j then 1 else 0)
    (hec : ∀ i, ContinuousOn (fun y => e y i) Y) {r : (X dim) → ℝ}
    (hrc : ContinuousOn r Y) (hr : ∀ y ∈ Y, 0 < r y ∧ r y < ρ)
    (hSphere : ∀ y ∈ Y, ∀ w : ↥(standardSphere dim), (E (y,r y • frameVector e y w),y) ∈ O)
    {y₀ : (X dim)} (hy₀ : y₀ ∈ Y) {U : Set (X dim)} (hU : IsOpen U)
    (hCover : closedBallImage γ E r y₀ ⊆ U) {u : (X dim) → ℝ} (hu : Harmonic U g₁ u) :
    ∃ V : Set (X dim), IsOpen V ∧ y₀ ∈ V ∧ V ⊆ Y ∧
      (∀ y ∈ V, closedBallImage γ E r y ⊆ U) ∧
      Harmonic V g₂ (fun y => normalSphereGreenFlux g₁ E e r G y u) := by
  obtain ⟨s,hs,hcap,hbig⟩ := exists_larger_normalBall_inside hU hE.continuous (he y₀ hy₀)
    (hr y₀ hy₀).1 (hr y₀ hy₀).2 hCover
  have hs₀ : 0 < s := (hr y₀ hy₀).1.trans hs
  have hEv := eventually_closedBallImage_subset hE.continuous hU (hY.mem_nhds hy₀) he
    (fun i => (hec i).continuousAt (hY.mem_nhds hy₀)) (r := fun _ => s) continuousAt_const hs₀ hbig
  have hRad : ∀ᶠ y in 𝓝 y₀, r y < s :=
    (hrc.continuousAt (hY.mem_nhds hy₀)).eventually (gt_mem_nhds hs)
  have hNear : {y | closedBallImage γ E (fun _ => s) y ⊆ U} ∩ {y | r y < s} ∩ Y ∈ 𝓝 y₀ :=
    inter_mem (inter_mem hEv hRad) (hY.mem_nhds hy₀)
  obtain ⟨V,hV,hVo,hyV⟩ := _root_.mem_nhds_iff.mp hNear
  have hVY : V ⊆ Y := fun y hy => (hV hy).2
  have hrV (y : (X dim)) (hy : y ∈ V) : 0 < r y ∧ r y < s := ⟨(hr y (hVY hy)).1,(hV hy).1.2⟩
  have hDisk (y v : (X dim)) (hv : v ∈ disk γ y s) : v ∈ disk γ y ρ :=
    hv.trans (pow_le_pow_left₀ hs₀.le hcap.le 2)
  have hNV : NormalCoordinates V U γ E (fun _ => s) := by
    refine ⟨⟨univ,isOpen_univ,subset_univ _,hE.contDiffOn⟩,fun y hy => ?_⟩
    obtain ⟨_,hInj,hYdata⟩ := hN.2 y (hVY hy)
    refine ⟨hs₀,hInj.mono (fun v hv => hDisk y v hv),fun v hv => ?_⟩
    exact ⟨(hV hy).1.1 ⟨v,hv,rfl⟩,(hYdata v (hDisk y v hv)).2⟩
  obtain ⟨hP,hPU,W,hW,hExact,hInv⟩ :=
    exists_normal_inverse_velocity hVo (smoothMetric_restrict hγ (subset_univ V)) hNV
  have heV (y : (X dim)) (hy : y ∈ V) := he y (hVY hy)
  have hSphereV y (hy : y ∈ V) := hSphere y (hVY hy)
  obtain ⟨T,hT,hTval⟩ := exists_harmonic_normalGreenTransfer hVo hU hγ hg₁ hE.continuous
    hP hPU hW.continuousOn hExact hInv hO hG heV (fun i => (hec i).mono hVY)
    (hrc.mono hVY) hrV hSphereV hu
  have hEq : EqOn (fun y => normalSphereGreenFlux g₁ E e r G y u) T V := by
    intro y hy
    obtain ⟨η,φ,hφ⟩ := exists_eventually_normalGreenCutoff hVo hU hγ hE.continuous hP hPU
      hW.continuousOn hExact hInv hO hy heV (fun i => (hec i).continuousAt (hY.mem_nhds (hVY hy)))
      (hrc.continuousAt (hY.mem_nhds (hVY hy))) (hrV y hy).1 (hrV y hy).2 (hSphereV y hy) hu.1
    have hφy := hφ.self_of_nhds
    exact (hφy.pairing_eq_normalSphereGreenFlux hU (smoothMetric_restrict hg₁ (subset_univ U))
      hE hNV hExact hInv hO hG hy (heV y hy) hu).symm.trans (hTval y hy η φ hφy).symm
  refine ⟨V,hVo,hyV,hVY,?_,⟨hT.1.congr hEq,?_⟩⟩
  · intro y hy x hx
    obtain ⟨v,hv,rfl⟩ := hx
    exact (hV hy).1.1 ⟨v,hv.trans (pow_le_pow_left₀ (hrV y hy).1.le (hrV y hy).2.le 2),rfl⟩
  · intro y hy
    exact (laplace_congrOn hVo (fun _ _ => rfl) hEq hy).trans (hT.2 y hy)

end CalderonN
