module

public import Proof.CalderonN.NormalBallChart
public import Proof.CalderonN.MetricPullback

import Mathlib.Tactic

@[expose] public section

noncomputable section
open Set Metric
open scoped ContDiff

namespace CalderonN

variable {dim : ℕ} [NeZero dim]

/-- A smooth first-metric Dirichlet test on the literal ball pulls back
to a harmonic test on the fixed unit ball, with the exact metric. -/
theorem harmonicOnBall_normalBallChartMap
    {Y Ω : Set (X dim)} (hΩ : IsOpen Ω) {γ g : (MetricField dim)} (hg : SmoothMetric Ω g)
    {ρ : ℝ} {E : (X dim) × (X dim) → (X dim)}
    (hE : ContDiff ℝ ∞ E) (hN : NormalCoordinates Y Ω γ E (fun _ => ρ))
    {e : (Frame dim)} {y : (X dim)} (hy : y ∈ Y)
    (he : ∀ i j, metricPair γ y (e y i) (e y j) = if i = j then 1 else 0)
    {r : (X dim) → ℝ} (hr : 0 < r y) (hR : r y < ρ)
    {u : (X dim) → ℝ} (hu : HarmonicOnBall g (closedBallImage γ E r y) u) :
    let F := normalBallChartMap E e y (r y)
    ∃ U : Set (X dim), IsOpen U ∧ closedBall (0 : (X dim)) 1 ⊆ U ∧ SmoothMetric U (pullbackMetric g F) ∧
      ContDiffOn ℝ ∞ (u ∘ F) U ∧ ∀ z ∈ ball (0 : (X dim)) 1, laplace (pullbackMetric g F) (u ∘ F) z = 0 := by
  let F := normalBallChartMap E e y (r y)
  let D := ball (0 : (X dim)) (ρ/r y)
  let B := ball (0 : (X dim)) 1
  let C := closedBall (0 : (X dim)) 1
  let N := closedBallImage γ E r y
  have hCD : C ⊆ D := closedBall_subset_ball ((lt_div_iff₀ hr).mpr (by simpa using hR))
  have hcF : ContDiff ℝ ∞ F := contDiff_normalBallChartMap hE e y (r y)
  have hFC : F '' C = N := (closedBallImage_eq_scaledFrameImage γ E e y he hr).symm
  obtain ⟨hInj,hMap,hBij⟩ := normalBallChartMap_on_openBall hE hN hy he hr
  have hBD : B ⊆ D := ball_subset_closedBall.trans hCD
  have hBimg : IsOpen (F '' B) :=
    (exists_smooth_inverse_on_image isOpen_ball hcF.contDiffOn (hInj.mono hBD)
      (fun z hz => hBij z (hBD hz))).1
  have hBN : F '' B ⊆ interior N :=
    hBimg.subset_interior_iff.mpr ((image_mono ball_subset_closedBall).trans_eq hFC)
  obtain ⟨V,hV,hNV,huV⟩ := hu.1
  let U := D ∩ F ⁻¹' V
  have hU : IsOpen U := isOpen_ball.inter (hV.preimage hcF.continuous)
  have hCU : C ⊆ U := by
    intro z hz
    refine ⟨hCD hz,hNV ?_⟩
    change F z ∈ N
    rw [← hFC]
    exact mem_image_of_mem F hz
  have hUV : MapsTo F U (Ω ∩ V) := fun z hz => ⟨hMap hz.1,hz.2⟩
  have hG : SmoothMetric (Ω ∩ V) g :=
    ⟨fun i j => (hg.1 i j).mono inter_subset_left,fun x hx => hg.2 x hx.1⟩
  have hG' : SmoothMetric U (pullbackMetric g F) :=
    smoothMetric_pullbackMetric hG hcF hUV (fun z hz => coordinateJacobian_det_ne_zero (hBij z hz.1))
  refine ⟨U,hU,hCU,hG',huV.comp hcF.contDiffOn (fun _ hz => hz.2),?_⟩
  intro z hz
  have hzU := hCU (ball_subset_closedBall hz)
  exact (laplace_pullbackMetric (hΩ.inter hV) hG hcF (huV.mono inter_subset_right)
    (hUV hzU) (coordinateJacobian_det_ne_zero (hBij z hzU.1))).trans
    (hu.2 (F z) (hBN (mem_image_of_mem F hz)))

end CalderonN
