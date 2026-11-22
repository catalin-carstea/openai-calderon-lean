module

public import Proof.CalderonN.CrossSeries
import Proof.CalderonN.GreenWeak
import Mathlib.Tactic.Ring

public section

noncomputable section
open Set Filter MeasureTheory
open scoped ENNReal

namespace CalderonN

variable {d : ℕ} [NeZero d]
open LocalMetricExtension

private abbrev chartMeasure (D : Set (X d)) : Measure (X d) := (volume : Measure (X d)).restrict D

theorem smoothMetric_restrict {D O : Set (X d)} {g : (MetricField d)}
    (hg : SmoothMetric D g) (hOD : O ⊆ D) : SmoothMetric O g :=
  ⟨fun i j => (hg.1 i j).mono hOD, fun x hx => hg.2 x (hOD hx)⟩

/-- Weak harmonicity is local on the chart, with the same volume density. -/
theorem harmonicRestrict_mem {D O : Set (X d)} (hD : IsOpen D) (hO : IsOpen O)
    {g : (MetricField d)} (hg : SmoothMetric D g) (hOD : O ⊆ D)
    (u : harmonicL2Space hD hg) :
    harmonicRestrict hD hg hOD u ∈ harmonicL2Space hO (smoothMetric_restrict hg hOD) := by
  obtain ⟨f, hf, hrep⟩ := harmonicL2Space_representative hD hg u
  apply (mem_harmonicL2Space_iff hO (smoothMetric_restrict hg hOD) _).mpr
  exact ⟨f, ⟨hf.1.mono hOD, fun x hx => hf.2 x (hOD hx)⟩,
    (harmonicRestrict_ae hD hg hOD u).trans (ae_mono (Measure.restrict_mono_set volume hOD) hrep)⟩

private theorem inner_tensorLp_tensorLp {D₁ D₂ : Set (X d)}
    (u a : ChartL2 (d := d) D₁) (v b : ChartL2 (d := d) D₂) :
    inner ℝ (tensorLp a b) (tensorLp u v) = inner ℝ a u * inner ℝ b v := by
  rw [L2.inner_def, L2.inner_def, L2.inner_def]
  calc
    _ = ∫ q, inner ℝ (a q.1) (u q.1) * inner ℝ (b q.2) (v q.2)
        ∂((chartMeasure D₁).prod (chartMeasure D₂)) := by
      apply integral_congr_ae
      filter_upwards [tensorLp_ae a b, tensorLp_ae u v] with q hab huv
      simp only [hab, huv, RCLike.inner_apply, conj_trivial]
      ring
    _ = _ := integral_prod_mul (μ := chartMeasure D₁) (ν := chartMeasure D₂)
      (L := ℝ) (fun x => inner ℝ (a x) (u x)) (fun y => inner ℝ (b y) (v y))

private def laplaceTestLp {D : Set (X d)} (hD : IsOpen D) {g : (MetricField d)} (hg : SmoothMetric D g)
    (φ : ChartTest D) : ChartL2 (d := d) D :=
  (test_laplace_memLp hD hg φ).toLp _

private theorem inner_laplaceTestLp_eq_zero {D : Set (X d)} (hD : IsOpen D)
    {g : (MetricField d)} (hg : SmoothMetric D g) {u : ChartL2 (d := d) D}
    (hu : u ∈ weakHarmonicL2Space hD hg) (φ : ChartTest D) :
    inner ℝ (laplaceTestLp hD hg φ) u = 0 := by
  rw [L2.inner_def]
  refine (integral_congr_ae ?_).trans ((mem_weakHarmonicL2Space_iff hD hg u).mp hu φ)
  filter_upwards [(test_laplace_memLp hD hg φ).coeFn_toLp] with x hx
  simp [laplaceTestLp, RCLike.inner_apply, hx]

/-- The two weak equations on the product, tested by one compact chart
test and an arbitrary square-integrable function in the other variable. -/
def WeakProductSolution {D₁ D₂ : Set (X d)} (hD₁ : IsOpen D₁) (hD₂ : IsOpen D₂)
    {g₁ g₂ : (MetricField d)} (hg₁ : SmoothMetric D₁ g₁) (hg₂ : SmoothMetric D₂ g₂)
    (Q : ChartProductL2 (d := d) D₁ D₂) : Prop :=
  (∀ φ : ChartTest D₁, ∀ v : ChartL2 (d := d) D₂, inner ℝ (tensorLp (laplaceTestLp hD₁ hg₁ φ) v) Q = 0) ∧
  ∀ u : ChartL2 (d := d) D₁, ∀ φ : ChartTest D₂, inner ℝ (tensorLp u (laplaceTestLp hD₂ hg₂ φ)) Q = 0

/-- Both distributional equations pass through the actual L² series limit. -/
theorem weakProductSolution_of_hasSum {D₁ D₂ : Set (X d)} (hD₁ : IsOpen D₁) (hD₂ : IsOpen D₂)
    {g₁ g₂ : (MetricField d)} (hg₁ : SmoothMetric D₁ g₁) (hg₂ : SmoothMetric D₂ g₂)
    {ι : Type*} {f : ι → ChartL2 (d := d) D₁} {b : ι → ChartL2 (d := d) D₂} {Q : ChartProductL2 (d := d) D₁ D₂}
    (hf : ∀ i, f i ∈ harmonicL2Space hD₁ hg₁) (hb : ∀ i, b i ∈ harmonicL2Space hD₂ hg₂)
    (hQ : HasSum (fun i => tensorLp (f i) (b i)) Q) :
    WeakProductSolution hD₁ hD₂ hg₁ hg₂ Q := by
  constructor
  · intro φ v
    have h := (innerSL ℝ (tensorLp (laplaceTestLp hD₁ hg₁ φ) v)).hasSum hQ
    have hz (i : ι) := inner_laplaceTestLp_eq_zero hD₁ hg₁ ((harmonicL2Space_le_weakHarmonicL2Space hD₁ hg₁) (hf i)) φ
    simp only [innerSL_apply_apply, inner_tensorLp_tensorLp, hz, zero_mul] at h
    exact h.unique hasSum_zero
  · intro u φ
    have h := (innerSL ℝ (tensorLp u (laplaceTestLp hD₂ hg₂ φ))).hasSum hQ
    have hz (i : ι) := inner_laplaceTestLp_eq_zero hD₂ hg₂ ((harmonicL2Space_le_weakHarmonicL2Space hD₂ hg₂) (hb i)) φ
    simp only [innerSL_apply_apply, inner_tensorLp_tensorLp, hz, mul_zero] at h
    exact h.unique hasSum_zero

end CalderonN
