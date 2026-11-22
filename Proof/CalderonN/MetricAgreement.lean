module

public import Proof.CalderonN.ShrinkingLimit

import Proof.CalderonN.ChartGeometry
import Proof.CalderonN.Conformal
import Mathlib.Analysis.Normed.Module.Connected

public section

noncomputable section
open Set Filter
open scoped ContDiff Topology

namespace CalderonN

variable {dim : ℕ} [NeZero dim]

theorem metric_eqOn_of_normalized_eq_inv (hn : 3 ≤ dim)
    {U : Set (X dim)} (hU : IsOpen U) (hconn : IsPreconnected U)
    {γ g₁ g₂ : (MetricField dim)} (hγ : SmoothMetric U γ)
    (hg₁ : SmoothMetric U g₁) (hg₂ : SmoothMetric U g₂)
    (h₁ : HarmonicCoordinates U g₁) (h₂ : HarmonicCoordinates U g₂)
    (hγ₁ : ∀ x ∈ U, ∃ a : ℝ, 0 < a ∧ γ x = a • g₁ x)
    (hQ : EqOn (principal γ g₂) (fun x => (γ x)⁻¹) U)
    {x₀ : (X dim)} (hx₀ : x₀ ∈ U) (hmatch : g₁ x₀ = g₂ x₀) :
    EqOn g₁ g₂ U := by
  let c (x : (X dim)) := g₂ x 0 0 / g₁ x 0 0
  have hc₁ (x : (X dim)) (hx : x ∈ U) : 0 < g₁ x 0 0 := (hg₁.2 x hx).diag_pos
  have hc₂ (x : (X dim)) (hx : x ∈ U) : 0 < g₂ x 0 0 := (hg₂.2 x hx).diag_pos
  have hc : DifferentiableOn ℝ c U :=
    ((hg₂.1 0 0).div (hg₁.1 0 0) fun x hx => (hc₁ x hx).ne').differentiableOn (by simp)
  have hpos : ∀ x ∈ U, 0 < c x := fun x hx => div_pos (hc₂ x hx) (hc₁ x hx)
  apply metric_eqOn_of_harmonic_conformal hn hU hconn hg₁ hg₂ h₁ h₂ hc hpos _ hx₀ hmatch
  intro x hx
  obtain ⟨a, _, ha⟩ := hγ₁ x hx
  obtain ⟨b, _, hb⟩ := exists_pos_smul_of_principal_eq_inv (hγ.2 x hx) (hg₂.2 x hx) (hQ hx)
  have hₓ : g₂ x = (b * a) • g₁ x := by rw [hb, ha, smul_smul]
  have hentry : g₂ x 0 0 = (b * a) * g₁ x 0 0 :=
    congrArg (fun A : (Mat dim) => A 0 0) hₓ
  have hcx : c x = b * a := by
    change g₂ x 0 0 / g₁ x 0 0 = b * a
    rw [hentry, mul_div_cancel_right₀ _ (hc₁ x hx).ne']
  change g₂ x = c x • g₁ x
  rw [hcx]
  exact hₓ

/-- Section 6 after obtaining the uniform strict gain on a fixed chart. -/
theorem exists_ball_metric_eq_of_origin_half_improvement (hn : 3 ≤ dim)
    {Ω K : Set (X dim)} (hΩ : IsOpen Ω)
    (hK : IsCompact K) (hKΩ : K ⊆ Ω) (h₀K : (0 : (X dim)) ∈ interior K)
    {γ g₁ g₂ : (MetricField dim)} (hγ : SmoothMetric Ω γ)
    (hg₁ : SmoothMetric Ω g₁) (hg₂ : SmoothMetric Ω g₂)
    (hchart₁ : HarmonicCoordinates Ω g₁) (hchart₂ : HarmonicCoordinates Ω g₂)
    (hγ₁ : ∀ x ∈ Ω, ∃ a : ℝ, 0 < a ∧ γ x = a • g₁ x)
    (hmatch : g₁ 0 = g₂ 0)
    {R ε : ℝ} (hR : 0 < R) (hε : 0 < ε) {p : ℕ} (hp : p ≠ 0)
    {depth : (X dim) → ℝ} (hdepth : ContinuousOn depth K) (hdepth₀ : depth 0 < 0)
    (hinitial : ∀ y ∈ K, smallJet γ g₂ y ≤ ε * shrinkingRadius R p depth 1 y)
    (himprove : ∀ δ ∈ Ioc (0 : ℝ) 1,
      (∀ y ∈ K, smallJet γ g₂ y ≤ ε * shrinkingRadius R p depth δ y) →
      ∀ y ∈ K, smallJet γ g₂ y ≤ ε / 2 * shrinkingRadius R p depth δ y) :
    ∃ r > 0, Metric.ball (0 : (X dim)) r ⊆ Ω ∧ EqOn g₁ g₂ (Metric.ball 0 r) := by
  have hKnhds : K ∈ 𝓝 (0 : (X dim)) := mem_interior_iff_mem_nhds.mp h₀K
  have hdepthnhds : {y | depth y < 0} ∈ 𝓝 (0 : (X dim)) :=
    (hdepth.continuousAt hKnhds).preimage_mem_nhds (Iio_mem_nhds hdepth₀)
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp (inter_mem hKnhds hdepthnhds)
  let U := Metric.ball (0 : (X dim)) r
  have hUΩ : U ⊆ Ω := fun x hx => hKΩ (hball hx).1
  have hzero : (0 : (X dim)) ∈ U := Metric.mem_ball_self hr
  have hsmooth {g : (MetricField dim)} (hg : SmoothMetric Ω g) : SmoothMetric U g :=
    ⟨fun i j => (hg.1 i j).mono hUΩ, fun x hx => hg.2 x (hUΩ hx)⟩
  have hchart {g : (MetricField dim)} (hg : HarmonicCoordinates Ω g) : HarmonicCoordinates U g :=
    fun i => ⟨(hg i).1.mono hUΩ, fun x hx => (hg i).2 x (hUΩ hx)⟩
  have hQ := normalized_eq_inv_of_half_improvement hΩ hK hKΩ hγ hg₂ hR hε hp hdepth
    hinitial himprove
  refine ⟨r, hr, hUΩ, metric_eqOn_of_normalized_eq_inv hn Metric.isOpen_ball
    Metric.isPreconnected_ball (hsmooth hγ) (hsmooth hg₁) (hsmooth hg₂)
    (hchart hchart₁) (hchart hchart₂) (fun x hx => hγ₁ x (hUΩ hx)) ?_ hzero hmatch⟩
  intro x hx
  exact hQ (show x ∈ {y ∈ K | depth y ≤ 0} from ⟨(hball hx).1, (hball hx).2.le⟩)

theorem exists_ball_metric_eq_of_half_improvement (hn : 3 ≤ dim)
    {Ω W K : Set (X dim)} (hΩ : IsOpen Ω) (hside : ContainsSmoothSide Ω W)
    (hK : IsCompact K) (hKΩ : K ⊆ Ω) (h₀K : (0 : (X dim)) ∈ interior K)
    {γ g₁ g₂ : (MetricField dim)} (hγ : SmoothMetric Ω γ)
    (hg₁ : SmoothMetric Ω g₁) (hg₂ : SmoothMetric Ω g₂)
    (hchart₁ : HarmonicCoordinates Ω g₁) (hchart₂ : HarmonicCoordinates Ω g₂)
    (hγ₁ : ∀ x ∈ Ω, ∃ a : ℝ, 0 < a ∧ γ x = a • g₁ x)
    (hmetric : EqOn g₁ g₂ W)
    {R ε : ℝ} (hR : 0 < R) (hε : 0 < ε) {p : ℕ} (hp : p ≠ 0)
    {depth : (X dim) → ℝ} (hdepth : ContinuousOn depth K) (hdepth₀ : depth 0 < 0)
    (hinitial : ∀ y ∈ K, smallJet γ g₂ y ≤ ε * shrinkingRadius R p depth 1 y)
    (himprove : ∀ δ ∈ Ioc (0 : ℝ) 1,
      (∀ y ∈ K, smallJet γ g₂ y ≤ ε * shrinkingRadius R p depth δ y) →
      ∀ y ∈ K, smallJet γ g₂ y ≤ ε / 2 * shrinkingRadius R p depth δ y) :
    ∃ r > 0, Metric.ball (0 : (X dim)) r ⊆ Ω ∧ EqOn g₁ g₂ (Metric.ball 0 r) := by
  have hzeroΩ := hKΩ (interior_subset h₀K)
  have hmatch : g₁ 0 = g₂ 0 := by
    ext i j
    exact eq_at_origin_of_eqOn_side hside
      ((hg₁.1 i j).continuousOn.continuousAt (hΩ.mem_nhds hzeroΩ))
      ((hg₂.1 i j).continuousOn.continuousAt (hΩ.mem_nhds hzeroΩ))
      (fun x hx => congrArg (fun A : (Mat dim) => A i j) (hmetric hx))
  exact exists_ball_metric_eq_of_origin_half_improvement hn hΩ hK hKΩ h₀K hγ hg₁ hg₂
    hchart₁ hchart₂ hγ₁ hmatch hR hε hp hdepth hdepth₀ hinitial himprove

end CalderonN
