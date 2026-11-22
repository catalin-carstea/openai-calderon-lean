module

public import Proof.CalderonN.CrossProductWeak
public import Proof.CalderonN.CrossRestrictionSpectrum
public import Proof.CalderonN.CrossWeakContinuation

import Proof.CalderonN.CrossOverlap
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.Tactic.Positivity

public section

noncomputable section
open Set Filter MeasureTheory
open scoped ENNReal

namespace CalderonN

variable {dim : ℕ} [NeZero dim]
open LocalMetricExtension

private abbrev chartMeasure (D : Set (X dim)) : Measure (X dim) := (volume : Measure (X dim)).restrict D

set_option maxHeartbeats 2000000 in
/-- Section 3.2 through the actual weak extension. The analytic inputs are
finite-rank approximation and interpolation estimates.
The output agrees on both cross arms, with uniform L² control. -/
theorem exists_uniform_weak_crossExtension (s N A₀ : ℕ) (B C₁ C₂ γ₁ γ₂ : ℝ)
    (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂) (hγ₂ : 0 < γ₂) (hγ₂' : γ₂ ≤ 1)
    (hmargin : 0 < γ₁ + γ₂ - 1) (hs : (dim : ℝ) < s * (γ₁ + γ₂ - 1)) :
    ∃ C : ℝ, 0 ≤ C ∧
    ∀ {D₁ D₂ S₁ S₂ O₁ O₂ : Set (X dim)}
      (hD₁ : IsOpen D₁) (hD₂ : IsOpen D₂) (_hc₁ : IsConnected D₁) (_hc₂ : IsConnected D₂)
      (_hS₁ : IsOpen S₁) (_hS₂ : IsOpen S₂) (_hne₁ : S₁.Nonempty) (_hne₂ : S₂.Nonempty)
      (hO₁ : IsOpen O₁) (hO₂ : IsOpen O₂)
      (hS₁D₁ : S₁ ⊆ D₁) (hS₂D₂ : S₂ ⊆ D₂) (hO₁D₁ : O₁ ⊆ D₁) (hO₂D₂ : O₂ ⊆ D₂)
      {g₁ g₂ : (MetricField dim)} (hg₁ : SmoothMetric D₁ g₁) (hg₂ : SmoothMetric D₂ g₂)
      (_hfinite : (volume : Measure (X dim)) D₂ ≠ ⊤)
      (_happrox : HasRestrictionApprox hD₁ hg₁ hS₁D₁ s N A₀ B)
      (_hfirst : HarmonicInterpolation hD₁ hg₁ hS₁D₁ hO₁D₁ C₁ γ₁)
      (_hsecond : HarmonicInterpolation hD₂ hg₂ hS₂D₂ hO₂D₂ C₂ γ₂)
      (q₁ : ChartProductL2 (d := dim) D₁ S₂) (q₂ : ChartProductL2 (d := dim) S₁ D₂) (F : (X dim) × (X dim) → ℝ)
      (_hq₁ : (q₁ : (X dim) × (X dim) → ℝ) =ᵐ[((volume : Measure (X dim)).restrict D₁).prod
        ((volume : Measure (X dim)).restrict S₂)] F)
      (_hq₂ : (q₂ : (X dim) × (X dim) → ℝ) =ᵐ[((volume : Measure (X dim)).restrict S₁).prod
        ((volume : Measure (X dim)).restrict D₂)] F)
      (_hF₁ : ∀ y ∈ S₂, Harmonic D₁ g₁ (fun x => F (x,y)))
      (_hF₂ : ∀ x ∈ S₁, Harmonic D₂ g₂ (fun y => F (x,y)))
      (M : ℝ) (_hM : 0 ≤ M) (_hm₁ : ‖q₁‖ ≤ M) (_hm₂ : ‖q₂‖ ≤ M),
      ∃ Q : ChartProductL2 O₁ O₂,
        WeakProductSolution hO₁ hO₂ (smoothMetric_restrict hg₁ hO₁D₁) (smoothMetric_restrict hg₂ hO₂D₂) Q ∧
        ‖Q‖ ≤ C * M ∧
        (Q : (X dim) × (X dim) → ℝ) =ᵐ[((volume : Measure (X dim)).restrict O₁).prod
          ((volume : Measure (X dim)).restrict (O₂ ∩ S₂))] F ∧
        (Q : (X dim) × (X dim) → ℝ) =ᵐ[((volume : Measure (X dim)).restrict (O₁ ∩ S₁)).prod
          ((volume : Measure (X dim)).restrict O₂)] F ∧
        ∃ (ι : Type) (_hc : Countable ι)
          (a : ι → harmonicL2Space hO₁ (smoothMetric_restrict hg₁ hO₁D₁))
          (b : ι → harmonicL2Space hO₂ (smoothMetric_restrict hg₂ hO₂D₂)),
          (Summable fun i => ‖tensorLp (a i).1 (b i).1‖) ∧
          HasSum (fun i => tensorLp (a i).1 (b i).1) Q := by
  classical
  obtain ⟨P, hP, hspec⟩ := exists_uniform_restrictionSpectrum s N A₀ B _ hmargin hs
  refine ⟨C₁ * C₂ * P, by positivity, ?_⟩
  intro D₁ D₂ S₁ S₂ O₁ O₂ hD₁ hD₂ hc₁ hc₂ hS₁ hS₂ hne₁ hne₂ hO₁ hO₂
    hS₁D₁ hS₂D₂ hO₁D₁ hO₂D₂ g₁ g₂ hg₁ hg₂ hfinite happ hfirst hsecond
    q₁ q₂ F hq₁ hq₂ hF₁ hF₂ M hM hm₁ hm₂
  obtain ⟨ι, w, μ, hcnt, hμ, _hle, heigen, hgram, hsum, hsumP⟩ := hspec hD₁ hg₁ hS₁D₁ happ
    (harmonicRestrict_injective hD₁ hc₁ hS₁ hne₁ hS₁D₁ hg₁)
  let : Countable ι := hcnt
  obtain ⟨b, Q, hlarge, hsmall, habs, hser, hQ⟩ :=
    exists_crossSeries_L2 hD₁ hD₂ hS₁.measurableSet hS₂.measurableSet hS₁D₁ hS₂D₂ hO₁D₁ hO₂D₂
      hg₁ hg₂ hfinite q₁ q₂ hq₁ hq₂ hF₁ hF₂ w μ hμ heigen hgram hC₁ hC₂ hM hγ₂ hγ₂'
      hfirst hsecond hm₁ hm₂ hsum hsumP
  have hweak := weakProductSolution_of_hasSum hO₁ hO₂ (smoothMetric_restrict hg₁ hO₁D₁)
    (smoothMetric_restrict hg₂ hO₂D₂)
    (fun i => harmonicRestrict_mem hD₁ hO₁ hg₁ hO₁D₁ (w i))
    (fun i => harmonicRestrict_mem hD₂ hO₂ hg₂ hO₂D₂ (b i)) hser
  refine ⟨Q, hweak, hQ.trans_eq ?_, ?_, ?_, ?_⟩
  · exact mul_right_comm (C₁ * C₂) M P
  · have hthin : (volume : Measure (X dim)) S₂ ≠ ⊤ :=
      ((measure_mono hS₂D₂).trans_lt (lt_top_iff_ne_top.mpr hfinite)).ne
    have hB : O₂ ∩ S₂ ⊆ S₂ := inter_subset_right
    have hB' : O₂ ∩ S₂ ⊆ O₂ := inter_subset_left
    let c i := harmonicRestrict hD₂ hg₂ hO₂D₂ (b i)
    have hcoef (i : ι) : (c i : (X dim) → ℝ) =ᵐ[chartMeasure (O₂ ∩ S₂)] tensorCoefficient (w i).1 q₁ := by
      have hOae := ae_mono (Measure.restrict_mono_set volume hB')
        (harmonicRestrict_ae hD₂ hg₂ hO₂D₂ (b i))
      have hSae := ae_mono (Measure.restrict_mono_set volume hB)
        (harmonicRestrict_ae hD₂ hg₂ hS₂D₂ (b i))
      rw [hsmall i] at hSae
      exact Filter.EventuallyEq.trans hOae (Filter.EventuallyEq.symm hSae)
    exact Filter.EventuallyEq.trans
      (crossSeries_ae_eq_firstArm hD₁ hg₁ hO₁D₁ hB hB' hthin w c q₁
        (ae_firstArm_slices hD₁ hS₂.measurableSet hg₁ hq₁ hF₁) hcoef habs hser)
      (ae_mono (Measure.prod_mono (Measure.restrict_mono_set volume hO₁D₁)
        (Measure.restrict_mono_set volume hB)) hq₁)
  · have hA : O₁ ∩ S₁ ⊆ S₁ := inter_subset_right
    have hA' : O₁ ∩ S₁ ⊆ O₁ := inter_subset_left
    let c i := harmonicRestrict hD₂ hg₂ hO₂D₂ (b i)
    have hcoef (i : ι) : (c i : (X dim) → ℝ) =ᵐ[chartMeasure O₂]
        crossArmCoefficient (harmonicRestrict hD₁ hg₁ hS₁D₁ (w i)) (μ i) q₂ := by
      simpa only [c, hlarge i] using harmonicRestrict_ae hD₂ hg₂ hO₂D₂ (b i)
    exact Filter.EventuallyEq.trans
      (crossSeries_ae_eq_secondArm hD₁ hg₁ hA hA' hO₁D₁ hS₁D₁ hO₂D₂ hfinite w μ hμ hgram c q₂
        (ae_secondArm_slices_mem_rangeClosure hD₁ hD₂ hc₂ hS₁.measurableSet hS₂ hne₂
          hS₁D₁ hS₂D₂ hg₁ hg₂ hfinite q₁ q₂ hq₁ hq₂ hF₁ hF₂) hcoef habs hser)
      (ae_mono (Measure.prod_mono (Measure.restrict_mono_set volume hA)
        (Measure.restrict_mono_set volume hO₂D₂)) hq₂)

  · let a (i : ι) : harmonicL2Space hO₁ (smoothMetric_restrict hg₁ hO₁D₁) :=
      ⟨harmonicRestrict hD₁ hg₁ hO₁D₁ (w i),
        harmonicRestrict_mem hD₁ hO₁ hg₁ hO₁D₁ (w i)⟩
    let c (i : ι) : harmonicL2Space hO₂ (smoothMetric_restrict hg₂ hO₂D₂) :=
      ⟨harmonicRestrict hD₂ hg₂ hO₂D₂ (b i),
        harmonicRestrict_mem hD₂ hO₂ hg₂ hO₂D₂ (b i)⟩
    exact ⟨ι,hcnt,a,c,habs,hser⟩

end CalderonN
