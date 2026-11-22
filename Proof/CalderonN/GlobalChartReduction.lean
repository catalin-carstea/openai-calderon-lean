module

public import Proof.CalderonN.ChartNormalization

import Proof.CalderonN.LocalChartExtension
import Proof.CalderonN.GreenWeak
import Mathlib.Tactic

@[expose] public section

noncomputable section
open Set Metric Filter
open scoped ContDiff Topology

namespace CalderonN

variable {dim : ℕ}

/-- The normalized theorem with globally smooth auxiliary metric fields.
The equations and the Green kernel laws are still imposed on the chart. -/
@[expose] def GlobalNormalizedLocalMetricExtension (normal : I dim) : Prop :=
  ∀ {Ω W : Set (X dim)}, IsOpen Ω → IsOpen W → W ⊆ Ω → ContainsAlignedSide normal Ω W →
    ∀ {g₁ g₂ : (MetricField dim)}, SmoothMetric univ g₁ → SmoothMetric univ g₂ → g₁ 0 = 1 → g₂ 0 = 1 →
      HarmonicCoordinates Ω g₁ → HarmonicCoordinates Ω g₂ →
    ∀ {G₁ G₂ : (X dim) × (X dim) → ℝ}, GreenGerm Ω g₁ G₁ → GreenGerm Ω g₂ G₂ →
      EqOn g₁ g₂ W → EqOn G₁ G₂ (OffDiagonal W) →
    ∀ {n : ℕ} {u₁ u₂ : Fin n → (X dim) → ℝ},
      (∀ a, Harmonic Ω g₁ (u₁ a)) → (∀ a, Harmonic Ω g₂ (u₂ a)) →
      (∀ a, EqOn (u₁ a) (u₂ a) W) → HessianSpanning g₁ u₁ →
      ∃ r > 0, ball (0 : (X dim)) r ⊆ Ω ∧ EqOn g₁ g₂ (ball 0 r)

/-- Smoothly completing both metric fields leaves the original Green
and harmonic equations, the known side, and the Hessian spanning intact
on the single smaller chart used by the analytic construction. -/
theorem normalizedLocalMetricExtension_of_global
    {normal : I dim} (hglobal : GlobalNormalizedLocalMetricExtension normal) : NormalizedLocalMetricExtension normal := by
  intro Ω W hΩ hW _hWΩ hside g₁ g₂ hg₁ hg₂ h₁ h₂ hchart₁ hchart₂ G₁ G₂ hG₁ hG₂ hmet hgreen
    n u₁ u₂ hu₁ hu₂ hpair hspan
  obtain ⟨V,s,hV,h₀V,hVΩ,hs,hs₀,hsd,hsideW⟩ := hside
  have h₀Ω : (0 : (X dim)) ∈ Ω := hVΩ h₀V
  obtain ⟨q₁,hq₁,hEq₁⟩ := exists_global_chart_metric hΩ (isCompact_singleton (x := (0 : (X dim))))
    (singleton_subset_iff.mpr h₀Ω) hg₁
  obtain ⟨q₂,hq₂,hEq₂⟩ := exists_global_chart_metric hΩ (isCompact_singleton (x := (0 : (X dim))))
    (singleton_subset_iff.mpr h₀Ω) hg₂
  have hnear := (((hEq₁ 0 (mem_singleton _)).and (hEq₂ 0 (mem_singleton _))).and (hΩ.mem_nhds h₀Ω))
  obtain ⟨r,hr,hnear'⟩ := Metric.mem_nhds_iff.mp hnear
  let D := ball (0 : (X dim)) r
  let T := W ∩ D
  have hD : IsOpen D := isOpen_ball
  have hDΩ : D ⊆ Ω := fun _ hx => (hnear' hx).2
  have hT : IsOpen T := hW.inter hD
  have he₁ : EqOn q₁ g₁ D := fun _ hx => (hnear' hx).1.1
  have he₂ : EqOn q₂ g₂ D := fun _ hx => (hnear' hx).1.2
  have hp₁ : q₁ 0 = 1 := (he₁ (mem_ball_self hr)).trans h₁
  have hp₂ : q₂ 0 = 1 := (he₂ (mem_ball_self hr)).trans h₂
  have hsT : ContainsAlignedSide normal D T :=
    ⟨V ∩ D,s,hV.inter hD,⟨h₀V,mem_ball_self hr⟩,inter_subset_right,hs.mono inter_subset_left,
      hs₀,hsd,fun _ hx => ⟨hsideW ⟨hx.1.1,hx.2⟩,hx.1.2⟩⟩
  have hh {g q : (MetricField dim)} (he : EqOn q g D) {f : (X dim) → ℝ} (hf : Harmonic Ω g f) :
      Harmonic D q f :=
    ⟨hf.1.mono hDΩ,fun x hx => (laplace_congrOn hD he (fun _ _ => rfl) hx).trans (hf.2 x (hDΩ hx))⟩
  have ha₁ : HarmonicCoordinates D q₁ := fun i => hh he₁ (hchart₁ i)
  have ha₂ : HarmonicCoordinates D q₂ := fun i => hh he₂ (hchart₂ i)
  have he₀ : q₁ 0 = g₁ 0 := he₁ (mem_ball_self hr)
  have hspan' : HessianSpanning q₁ u₁ := by simpa only [HessianSpanning,he₀] using hspan
  have hmet' : EqOn q₁ q₂ T := fun x hx => (he₁ hx.2).trans ((hmet hx.1).trans (he₂ hx.2).symm)
  have hgreen' : EqOn G₁ G₂ (OffDiagonal T) :=
    fun _ hx => hgreen ⟨hx.1.1,hx.2.1.1,hx.2.2⟩
  obtain ⟨R,hR,hRD,hAgree⟩ := hglobal hD hT inter_subset_right hsT hq₁ hq₂ hp₁ hp₂ ha₁ ha₂
    (hG₁.restrict_congr_metric hΩ hD hDΩ hg₁ he₁.symm)
    (hG₂.restrict_congr_metric hΩ hD hDΩ hg₂ he₂.symm)
    hmet' hgreen' (fun i => hh he₁ (hu₁ i)) (fun i => hh he₂ (hu₂ i))
    (fun i x hx => hpair i hx.1) hspan'
  exact ⟨R,hR,hRD.trans hDΩ,fun x hx =>
    (he₁ (hRD hx)).symm.trans ((hAgree hx).trans (he₂ (hRD hx)))⟩

end CalderonN
