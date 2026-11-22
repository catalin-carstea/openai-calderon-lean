module

public import Proof.CalderonN.ChartNormalization
public import Proof.CalderonN.GreenCross
public import Proof.CalderonN.GreenDilation

import Proof.CalderonN.LocalChartExtension
import Proof.CalderonN.GreenWeak
import Mathlib.Tactic

public section

open CalderonN Set Metric Filter
open scoped Topology

namespace CalderonPaper

variable {n : ℕ}

/-- A smaller normalized chart retains the two original Green germs after
extending both metric fields to globally smooth positive fields.
The cutoff step follows `GlobalChartReduction.lean` in the checked package. -/
theorem exists_global_alignedGreen_chart
    {normal : I n} {Ω W : Set (X n)} (hΩ : IsOpen Ω)
    (hside : ContainsAlignedSide normal Ω W)
    {g₁ g₂ : MetricField n} (hg₁ : SmoothMetric Ω g₁) (hg₂ : SmoothMetric Ω g₂)
    {G₁ G₂ : (X n) × (X n) → ℝ} (hG₁ : GreenGerm Ω g₁ G₁) (hG₂ : GreenGerm Ω g₂ G₂)
    (hmetric : EqOn g₁ g₂ W) (hgreen : EqOn G₁ G₂ (OffDiagonal W)) :
    ∃ (r : ℝ) (q₁ q₂ : MetricField n), 0 < r ∧
      let D := ball (0 : X n) r
      let T := W ∩ D
      D ⊆ Ω ∧ ContainsAlignedSide normal D T ∧
      SmoothMetric univ q₁ ∧ SmoothMetric univ q₂ ∧
      EqOn q₁ g₁ D ∧ EqOn q₂ g₂ D ∧
      GreenGerm D q₁ G₁ ∧ GreenGerm D q₂ G₂ ∧
      EqOn q₁ q₂ T ∧ EqOn G₁ G₂ (OffDiagonal T) := by
  obtain ⟨V, s, hV, h₀V, hVΩ, hs, hs₀, hsd, hsideW⟩ := hside
  have h₀Ω : (0 : X n) ∈ Ω := hVΩ h₀V
  obtain ⟨q₁, hq₁, hEq₁⟩ := exists_global_chart_metric hΩ
    (isCompact_singleton (x := (0 : X n))) (singleton_subset_iff.mpr h₀Ω) hg₁
  obtain ⟨q₂, hq₂, hEq₂⟩ := exists_global_chart_metric hΩ
    (isCompact_singleton (x := (0 : X n))) (singleton_subset_iff.mpr h₀Ω) hg₂
  have hnear := ((hEq₁ 0 (mem_singleton _)).and (hEq₂ 0 (mem_singleton _))).and (hΩ.mem_nhds h₀Ω)
  obtain ⟨r, hr, hnear'⟩ := Metric.mem_nhds_iff.mp hnear
  let D := ball (0 : X n) r
  let T := W ∩ D
  have hD : IsOpen D := isOpen_ball
  have hDΩ : D ⊆ Ω := fun _ hx => (hnear' hx).2
  have he₁ : EqOn q₁ g₁ D := fun _ hx => (hnear' hx).1.1
  have he₂ : EqOn q₂ g₂ D := fun _ hx => (hnear' hx).1.2
  have hsT : ContainsAlignedSide normal D T :=
    ⟨V ∩ D, s, hV.inter hD, ⟨h₀V, mem_ball_self hr⟩, inter_subset_right, hs.mono inter_subset_left,
      hs₀, hsd, fun _ hx => ⟨hsideW ⟨hx.1.1, hx.2⟩, hx.1.2⟩⟩
  have hmet' : EqOn q₁ q₂ T := fun x hx => (he₁ hx.2).trans ((hmetric hx.1).trans (he₂ hx.2).symm)
  have hgreen' : EqOn G₁ G₂ (OffDiagonal T) :=
    fun _ hx => hgreen ⟨hx.1.1, hx.2.1.1, hx.2.2⟩
  exact ⟨r, q₁, q₂, hr, hDΩ, hsT, hq₁, hq₂, he₁, he₂,
    hG₁.restrict_congr_metric hΩ hD hDΩ hg₁ he₁.symm,
    hG₂.restrict_congr_metric hΩ hD hDΩ hg₂ he₂.symm, hmet', hgreen'⟩

/-- Each fixed bounded region eventually lies in the dilation of a
neighborhood of the origin. -/
theorem eventually_dilated_closedBall_mapsTo {D : Set (X n)} (hD : IsOpen D)
    (h0 : (0 : X n) ∈ D) (B : ℝ) :
    ∀ᶠ lam in 𝓝 (0 : ℝ), MapsTo (fun x : X n => lam • x) (closedBall 0 B) D := by
  apply (isCompact_closedBall (0 : X n) B).eventually_forall_of_forall_eventually
  intro x _
  have ht : ContinuousAt (fun q : ℝ × (X n) => q.1 • q.2) (0,x) :=
    (continuous_fst.smul continuous_snd).continuousAt
  exact ht.preimage_mem_nhds (by simpa only [zero_smul] using hD.mem_nhds h0)

/-- A product solution uses the same equations after a metric replacement
on an open coordinate patch containing both factors. -/
theorem productSolution_congr_metrics
    {D : Set (X n)} (hD : IsOpen D) {g₁ g₂ q₁ q₂ : MetricField n}
    (h₁ : EqOn q₁ g₁ D) (h₂ : EqOn q₂ g₂ D)
    {U : Set ((X n) × (X n))} (hU : U ⊆ D ×ˢ D)
    {F : (X n) × (X n) → ℝ} (hF : ProductSolutionOn q₁ q₂ U F) :
    ProductSolutionOn g₁ g₂ U F := by
  refine ⟨hF.1, ?_, ?_⟩
  · intro z hz
    rw [← laplace_congrOn hD h₁ (fun _ _ => rfl) (hU hz).1]
    exact hF.2.1 z hz
  · intro z hz
    rw [← laplace_congrOn hD h₂ (fun _ _ => rfl) (hU hz).2]
    exact hF.2.2 z hz

end CalderonPaper
