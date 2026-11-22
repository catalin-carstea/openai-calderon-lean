module

public import Proof.CalderonN.CrossSeries
public import Proof.CalderonN.CrossSeriesAgreement

import Mathlib.MeasureTheory.Measure.Prod

public section

noncomputable section
open Set Filter MeasureTheory
open scoped ENNReal

namespace CalderonN

variable {dim : ℕ} [NeZero dim]
open LocalMetricExtension

private abbrev chartMeasure (D : Set (X dim)) : Measure (X dim) := (volume : Measure (X dim)).restrict D

/-- The original Hilbert expansion gives first-arm agreement, including
the case in which only a portion of the observed second arm overlaps. -/
theorem crossSeries_ae_eq_firstArm
    {D₁ S₂ O₁ O₂ B : Set (X dim)} (hD₁ : IsOpen D₁) {g₁ : (MetricField dim)} (hg₁ : SmoothMetric D₁ g₁)
    (hO₁ : O₁ ⊆ D₁) (hBS : B ⊆ S₂) (hBO : B ⊆ O₂)
    (hfinite : (volume : Measure (X dim)) S₂ ≠ ⊤)
    {ι : Type*} [Countable ι] (w : HilbertBasis ι ℝ (harmonicL2Space hD₁ hg₁))
    (b : ι → ChartL2 O₂) (q : ChartProductL2 (d := dim) D₁ S₂)
    (hslice : ∀ᵐ y ∂(volume : Measure (X dim)).restrict S₂, ∃ u : harmonicL2Space hD₁ hg₁,
      (u.1 : (X dim) → ℝ) =ᵐ[(volume : Measure (X dim)).restrict D₁] fun x => q (x,y))
    (hb : ∀ i, (b i : (X dim) → ℝ) =ᵐ[(volume : Measure (X dim)).restrict B] tensorCoefficient (w i).1 q)
    {Q : ChartProductL2 O₁ O₂}
    (habs : Summable fun i => ‖tensorLp (harmonicRestrict hD₁ hg₁ hO₁ (w i)) (b i)‖)
    (hQ : HasSum (fun i => tensorLp (harmonicRestrict hD₁ hg₁ hO₁ (w i)) (b i)) Q) :
    (Q : (X dim) × (X dim) → ℝ) =ᵐ[((volume : Measure (X dim)).restrict O₁).prod ((volume : Measure (X dim)).restrict B)] q := by
  let hm := Measure.restrict_mono_set (volume : Measure (X dim)) hO₁
  let hn := Measure.restrict_mono_set (volume : Measure (X dim)) hBS
  let hn' := Measure.restrict_mono_set (volume : Measure (X dim)) hBO
  let : IsFiniteMeasure (chartMeasure S₂) := isFiniteMeasure_restrict.mpr hfinite
  let q' := restrictL2 (Measure.prod_mono hm hn) q
  have hq' := restrictL2_ae (Measure.prod_mono hm hn) q
  have hqswap := (Measure.measurePreserving_swap (μ := chartMeasure B)
    (ν := chartMeasure O₁)).quasiMeasurePreserving.ae hq'
  have hcoef (i : ι) : ∀ᵐ y ∂chartMeasure B,
      b i y = ∫ x, (w i).1 x * q (x,y) ∂chartMeasure D₁ := by
    exact Filter.EventuallyEq.trans (hb i) (ae_mono hn (tensorCoefficient_ae_integral (w i).1 q))
  refine Filter.EventuallyEq.trans (tensorSeries_ae_eq_of_slice_hasSum le_rfl hn'
    _ b habs hQ q' ?_) hq'
  filter_upwards [ae_mono hn hslice, ae_all_iff.mpr hcoef, Measure.ae_ae_of_ae_prod hqswap]
    with y hy hyb hys
  obtain ⟨u, hu⟩ := hy
  let R := harmonicRestrict hD₁ hg₁ hO₁
  refine ⟨R u, ?_, ?_⟩
  · have hentry : (fun x => q' (x,y)) =ᵐ[chartMeasure O₁] fun x => q (x,y) := hys
    exact (harmonicRestrict_ae hD₁ hg₁ hO₁ u).trans
      (Filter.EventuallyEq.trans (ae_mono hm hu) hentry.symm)
  · have hyre (i : ι) : b i y = inner ℝ (w i) u := by
      rw [hyb i]
      change _ = inner ℝ (w i).1 u.1
      rw [L2.inner_def]
      apply integral_congr_ae
      filter_upwards [hu] with x hx
      rw [RCLike.inner_apply, conj_trivial, hx, mul_comm]
    have hre (i : ι) : restrictL2 le_rfl (R (w i)) = R (w i) :=
      Lp.ext (restrictL2_ae le_rfl (R (w i)))
    change HasSum (fun i => b i y • restrictL2 le_rfl (R (w i))) (R u)
    simpa only [hyre, hre, map_smul, w.repr_apply_apply] using R.hasSum (w.hasSum_repr u)

set_option maxHeartbeats 900000 in
/-- The restricted singular basis reconstructs the second arm wherever
its actual slices belong to the closed restriction range. -/
theorem crossSeries_ae_eq_secondArm
    {D₁ D₂ S₁ O₁ O₂ A : Set (X dim)} (hD₁ : IsOpen D₁) {g₁ : (MetricField dim)} (hg₁ : SmoothMetric D₁ g₁)
    (hAS : A ⊆ S₁) (hAO : A ⊆ O₁) (hO₁ : O₁ ⊆ D₁) (hS₁ : S₁ ⊆ D₁) (hO₂ : O₂ ⊆ D₂)
    (hfinite : (volume : Measure (X dim)) D₂ ≠ ⊤)
    {ι : Type*} [Countable ι] [DecidableEq ι]
    (w : HilbertBasis ι ℝ (harmonicL2Space hD₁ hg₁)) (μ : ι → ℝ) (hμ : ∀ i, 0 < μ i)
    (hgram : ∀ i j, inner ℝ (harmonicRestrict hD₁ hg₁ hS₁ (w i))
      (harmonicRestrict hD₁ hg₁ hS₁ (w j)) = if i = j then μ i ^ 2 else 0)
    (b : ι → ChartL2 O₂) (q : ChartProductL2 (d := dim) S₁ D₂)
    (hslice : ∀ᵐ y ∂(volume : Measure (X dim)).restrict D₂,
      ∃ u ∈ closure (range (harmonicRestrict hD₁ hg₁ hS₁)),
        (u : (X dim) → ℝ) =ᵐ[(volume : Measure (X dim)).restrict S₁] fun x => q (x,y))
    (hb : ∀ i, (b i : (X dim) → ℝ) =ᵐ[(volume : Measure (X dim)).restrict O₂]
      crossArmCoefficient (harmonicRestrict hD₁ hg₁ hS₁ (w i)) (μ i) q)
    {Q : ChartProductL2 O₁ O₂}
    (habs : Summable fun i => ‖tensorLp (harmonicRestrict hD₁ hg₁ hO₁ (w i)) (b i)‖)
    (hQ : HasSum (fun i => tensorLp (harmonicRestrict hD₁ hg₁ hO₁ (w i)) (b i)) Q) :
    (Q : (X dim) × (X dim) → ℝ) =ᵐ[((volume : Measure (X dim)).restrict A).prod ((volume : Measure (X dim)).restrict O₂)] q := by
  let hm := Measure.restrict_mono_set (volume : Measure (X dim)) hAS
  let hm' := Measure.restrict_mono_set (volume : Measure (X dim)) hAO
  let hn := Measure.restrict_mono_set (volume : Measure (X dim)) hO₂
  let : IsFiniteMeasure (chartMeasure D₂) := isFiniteMeasure_restrict.mpr hfinite
  let q' := restrictL2 (Measure.prod_mono hm hn) q
  let R := harmonicRestrict hD₁ hg₁ hS₁
  let J := harmonicRestrict hD₁ hg₁ hO₁
  have hq' := restrictL2_ae (Measure.prod_mono hm hn) q
  have hqswap := (Measure.measurePreserving_swap (μ := chartMeasure O₂)
    (ν := chartMeasure A)).quasiMeasurePreserving.ae hq'
  have hcoef (i : ι) : ∀ᵐ y ∂chartMeasure O₂,
      b i y = (μ i ^ 2)⁻¹ * ∫ x, R (w i) x * q (x,y) ∂chartMeasure S₁ :=
    Filter.EventuallyEq.trans (hb i) (ae_mono hn (crossArmCoefficient_ae_integral (R (w i)) (μ i) q))
  refine Filter.EventuallyEq.trans (tensorSeries_ae_eq_of_slice_hasSum hm' le_rfl
    (fun i => J (w i)) b habs hQ q' ?_) hq'
  filter_upwards [ae_mono hn hslice, ae_all_iff.mpr hcoef, Measure.ae_ae_of_ae_prod hqswap]
    with y hy hyb hys
  obtain ⟨u, huR, hu⟩ := hy
  refine ⟨restrictL2 hm u, ?_, ?_⟩
  · have hentry : (fun x => q' (x,y)) =ᵐ[chartMeasure A] fun x => q (x,y) := hys
    exact (restrictL2_ae hm u).trans
      (Filter.EventuallyEq.trans (ae_mono hm hu) hentry.symm)
  · have hyre (i : ι) : b i y = singularCoefficient R w μ i u := by
      rw [hyb i, singularCoefficient_apply, L2.inner_def]
      congr 1
      apply integral_congr_ae
      filter_upwards [hu] with x hx
      rw [RCLike.inner_apply, conj_trivial, hx, mul_comm]
    have hre (i : ι) : restrictL2 hm (R (w i)) = restrictL2 hm' (J (w i)) := by
      apply Lp.ext
      exact ((restrictL2_ae hm (R (w i))).trans (ae_mono hm
        (harmonicRestrict_ae hD₁ hg₁ hS₁ (w i)))).trans
        ((restrictL2_ae hm' (J (w i))).trans (ae_mono hm'
          (harmonicRestrict_ae hD₁ hg₁ hO₁ (w i)))).symm
    have hgram' (i j : ι) : inner ℝ (R (w i)) (R (w j)) =
        @ite ℝ (i = j) (Classical.propDecidable _) (μ i ^ 2) 0 := by
      by_cases h : i = j
      · simp only [ite_eq_left h]
        simpa only [ite_eq_left h] using hgram i j
      · simp only [ite_eq_right h]
        simpa only [ite_eq_right h] using hgram i j
    simpa only [hyre, ← hre, map_smul] using
      (restrictL2 hm).hasSum (hasSum_singularCoefficient_closure R μ w hμ hgram' huR)

end CalderonN
