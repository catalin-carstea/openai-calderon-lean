module

public import Proof.CalderonN.FixedBallDirichletUnique
public import Proof.CalderonN.NormalBallHarmonic

import Proof.CalderonN.MovingCutoffGeometry
import Proof.CalderonN.GreenWeak
import Proof.CalderonN.ChartGeometry
import Proof.CalderonN.ChartUniqueContinuation
import Proof.CalderonN.FramePullback
import Proof.CalderonN.HarmonicL2Space
import Mathlib.Tactic

@[expose] public section

noncomputable section
open Set Metric
open scoped ContDiff Topology

namespace CalderonN

variable {dim : ℕ} [NeZero dim] [Nontrivial (Fin dim)]

set_option maxHeartbeats 1200000 in
/-- Transfer a smooth harmonic fixed-ball solution through the literal
normal chart, preserving its angular boundary value. -/
theorem exists_harmonicOnBall_of_normalBallChartMap
    {Y Ω : Set (X dim)} {γ g : (MetricField dim)} (hg : SmoothMetric Ω g)
    {ρ : ℝ} {E : (X dim) × (X dim) → (X dim)}
    (hE : ContDiff ℝ ∞ E) (hN : NormalCoordinates Y Ω γ E (fun _ => ρ))
    {e : (Frame dim)} {y : (X dim)} (hy : y ∈ Y)
    (he : ∀ i j, metricPair γ y (e y i) (e y j) = if i = j then 1 else 0)
    {r : (X dim) → ℝ} (hr : 0 < r y) (hR : r y < ρ)
    {b : (X dim) → ℝ} (hb : smoothNear b (closedBall (0 : (X dim)) 1))
    (hLap : ∀ z ∈ ball (0 : (X dim)) 1,
      laplace (pullbackMetric g (normalBallChartMap E e y (r y))) b z = 0) :
    ∃ u, HarmonicOnBall g (closedBallImage γ E r y) u ∧
      EqOn (u ∘ normalBallChartMap E e y (r y)) b (closedBall (0 : (X dim)) 1) := by
  let F := normalBallChartMap E e y (r y)
  let D := ball (0 : (X dim)) (ρ/r y)
  let B := ball (0 : (X dim)) 1
  let C := closedBall (0 : (X dim)) 1
  let N := closedBallImage γ E r y
  have hCD : C ⊆ D := closedBall_subset_ball ((lt_div_iff₀ hr).mpr (by simpa using hR))
  have hcF : ContDiff ℝ ∞ F := contDiff_normalBallChartMap hE e y (r y)
  have hFC : F '' C = N := (closedBallImage_eq_scaledFrameImage γ E e y he hr).symm
  obtain ⟨hInj,hMap,hBij⟩ := normalBallChartMap_on_openBall hE hN hy he hr
  obtain ⟨hFD,v,hv,hL,hV,hR'⟩ :=
    exists_smooth_inverse_on_image isOpen_ball hcF.contDiffOn hInj hBij
  obtain ⟨S,hS,hCS,hbS⟩ := hb
  let W := (F '' D) ∩ v ⁻¹' S
  have hW : IsOpen W := hv.continuousOn.isOpen_inter_preimage hFD hS
  have hWN : N ⊆ W := by
    rw [← hFC]
    rintro x ⟨z,hz,rfl⟩
    exact ⟨mem_image_of_mem F (hCD hz),by change v (F z) ∈ S; rw [hL (hCD hz)]; exact hCS hz⟩
  have hWΩ : W ⊆ Ω := by
    intro x hx
    obtain ⟨z,hz,rfl⟩ := hx.1
    exact hMap hz
  let u := b ∘ v
  have hu : ContDiffOn ℝ ∞ u W :=
    hbS.comp (hv.mono inter_subset_left) (fun _ hx => hx.2)
  have heV : EqOn (u ∘ F) b (D ∩ S) := fun z hz => congrArg b (hL hz.1)
  refine ⟨u,⟨⟨W,hW,hWN,hu⟩,?_⟩,heV.mono (show C ⊆ D ∩ S from fun z hz => ⟨hCD hz,hCS hz⟩)⟩
  intro x hx
  have hxN := interior_subset hx
  have hxW := hWN hxN
  let z := v x
  have hzD : z ∈ D := hV hxW.1
  have hFz : F z = x := hR' hxW.1
  have hzS : z ∈ S := hxW.2
  have hzB : z ∈ B := by
    have hN' : z ∈ D ∩ F ⁻¹' interior N := ⟨hzD,by change F z ∈ interior N; rwa [hFz]⟩
    have hopen : IsOpen (D ∩ F ⁻¹' interior N) :=
      isOpen_ball.inter (isOpen_interior.preimage hcF.continuous)
    have hsub : D ∩ F ⁻¹' interior N ⊆ C := by
      intro q hq
      have hqN : F q ∈ N := interior_subset hq.2
      rw [← hFC] at hqN
      obtain ⟨q',hq',hqq'⟩ := hqN
      rwa [hInj hq.1 (hCD hq') hqq'.symm]
    have hI := hopen.subset_interior_iff.mpr hsub hN'
    simpa only [C,B,interior_closedBall _ one_ne_zero] using hI
  have hgW : SmoothMetric W g :=
    ⟨fun i j => (hg.1 i j).mono hWΩ,fun x hx => hg.2 x (hWΩ hx)⟩
  have hJac := coordinateJacobian_det_ne_zero (hBij z hzD)
  have hPull := laplace_pullbackMetric hW hgW hcF hu (show F z ∈ W from hFz.symm ▸ hxW) hJac
  rw [hFz] at hPull
  have hEq := laplace_congrOn (g := pullbackMetric g F) (h := pullbackMetric g F)
    (isOpen_ball.inter hS) (fun _ _ => rfl) heV ⟨hzD,hzS⟩
  exact hPull.symm.trans (hEq.trans (hLap z hzB))

set_option maxHeartbeats 1200000 in
/-- A solver on the fixed unit ball gives the protected Dirichlet
property on the actual family of normal balls. -/
theorem normalDirichlet_of_fixedBall
    {Y Ω : Set (X dim)} (hΩ : IsOpen Ω) {γ g : (MetricField dim)} (hg : SmoothMetric Ω g)
    {ρ : ℝ} {E : (X dim) × (X dim) → (X dim)} (hE : ContDiff ℝ ∞ E)
    (hN : NormalCoordinates Y Ω γ E (fun _ => ρ))
    {e : (Frame dim)} (he : ∀ y ∈ Y, ∀ i j, metricPair γ y (e y i) (e y j) = if i = j then 1 else 0)
    {r : (X dim) → ℝ} (hr : ∀ y ∈ Y, 0 < r y ∧ r y < ρ)
    (hSolve : ∀ y ∈ Y, ∀ a : (X dim) → ℝ, smoothNear a (standardSphere dim) →
      ∃ b : (X dim) → ℝ, smoothNear b (closedBall (0 : (X dim)) 1) ∧ EqOn b a (standardSphere dim) ∧
        ∀ z ∈ ball (0 : (X dim)) 1, laplace (pullbackMetric g (normalBallChartMap E e y (r y))) b z = 0) :
    Dirichlet Y γ g E r := by
  intro y hy a ha
  let F := normalBallChartMap E e y (r y)
  let V := frameVector e y
  let N := closedBallImage γ E r y
  let C := closedBall (0 : (X dim)) 1
  have hEqN : N = F '' C := closedBallImage_eq_scaledFrameImage γ E e y (he y hy) (hr y hy).1
  have hf : ContDiff ℝ ∞ V := by
    change ContDiff ℝ ∞ (frameVector e y)
    rw [show frameVector e y = frameVectorLinear e y from funext (fun z => (frameVectorLinear_apply _ _ z).symm)]
    exact (frameVectorLinear e y).contDiff
  have hV (z : (X dim)) (hz : z ∈ (standardSphere dim)) : V z ∈ sphereAt γ y :=
    frameVector_mem_sphere γ e y (he y hy) ⟨z,hz⟩
  obtain ⟨U,hU,hSub,haU⟩ := ha
  have hVa : smoothNear (a ∘ V) (standardSphere dim) := by
    refine ⟨V ⁻¹' U,hU.preimage hf.continuous,fun z hz => hSub (hV z hz),?_⟩
    exact haU.comp hf.contDiffOn (fun _ h => h)
  obtain ⟨b,hb,hB,hP⟩ := hSolve y hy (a ∘ V) hVa
  obtain ⟨u,hu,hUF⟩ := exists_harmonicOnBall_of_normalBallChartMap hg hE hN
    hy (he y hy) (hr y hy).1 (hr y hy).2 hb hP
  have hExists : ∀ v ∈ sphereAt γ y, ∃ z ∈ (standardSphere dim), V z = v := by
    intro v hv
    let z := frameCoordinates γ y (e y) v
    have hNorm := norm_frameCoordinates_sq γ y v (e y) (he y hy)
    rw [show metricPair γ y v v = 1 from hv] at hNorm
    change ‖z‖^2 = 1 at hNorm
    have hz₀ : ‖z‖ = 1 := by nlinarith [norm_nonneg z]
    refine ⟨z,by simpa only [standardSphere,mem_sphere,dist_zero_right] using hz₀,?_⟩
    exact frameVector_frameCoordinates γ y v (e y) (he y hy)
  have hBdy : ∀ v ∈ sphereAt γ y, u (endpoint E r (y,v)) = a v := by
    intro v hv
    obtain ⟨z,hz,h⟩ := hExists v hv
    rw [← h]
    exact (hUF (sphere_subset_closedBall hz)).trans (hB hz)
  refine ⟨u,⟨hu,hBdy⟩,?_⟩
  intro u' hu'
  obtain ⟨S,hS,hCS,hgS,huS,hLu⟩ := harmonicOnBall_normalBallChartMap hΩ hg hE hN
    hy (he y hy) (hr y hy).1 (hr y hy).2 hu
  obtain ⟨T,hT,hCT,_,hu'T,hLu'⟩ := harmonicOnBall_normalBallChartMap hΩ hg hE hN
    hy (he y hy) (hr y hy).1 (hr y hy).2 hu'.1
  let M := pullbackMetric g F
  have hST : IsOpen (S ∩ T) := hS.inter hT
  have hCST : C ⊆ S ∩ T := fun z hz => ⟨hCS hz,hCT hz⟩
  have hMetric : SmoothMetric (S ∩ T) M :=
    ⟨fun i j => (hgS.1 i j).mono inter_subset_left,fun z hz => hgS.2 z hz.1⟩
  have huST : ContDiffOn ℝ ∞ (u ∘ F) (S ∩ T) := huS.mono inter_subset_left
  have hu'ST : ContDiffOn ℝ ∞ (u' ∘ F) (S ∩ T) := hu'T.mono inter_subset_right
  have hDiff := eqOn_closedUnitBall_of_laplace_eq_zero hST hCST hMetric
    (huST.sub hu'ST) (by
      intro z hz
      have hzST := hCST (ball_subset_closedBall hz)
      rw [laplace_sub hST M huST hu'ST hzST,hLu z hz,hLu' z hz,sub_zero]) (by
      intro z hz
      change u (endpoint E r (y,V z)) - u' (endpoint E r (y,V z)) = 0
      rw [hBdy _ (hV z hz), hu'.2 _ (hV z hz), sub_self])
  intro x hx
  change x ∈ N at hx
  obtain ⟨z,hz,rfl⟩ := hEqN ▸ hx
  exact sub_eq_zero.mp (hDiff hz)

end CalderonN
