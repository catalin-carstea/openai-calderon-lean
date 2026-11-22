module

public import Proof.CalderonN.CrossArmCoefficients

import Mathlib.MeasureTheory.Function.LpSpace.InfiniteSum
import Mathlib.Order.Filter.AtTopBot.CountablyGenerated

public section

open MeasureTheory Filter
open scoped ENNReal Topology

namespace LocalMetricExtension

/-- A norm-summable product series agrees on a smaller rectangle with
any kernel whose slices have the same Hilbert expansion there. -/
theorem tensorSeries_ae_eq_of_slice_hasSum
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {m m' : Measure α} {n n' : Measure β}
    [SFinite m] [SFinite m'] [SFinite n] [SFinite n']
    (hm : m' ≤ m) (hn : n' ≤ n)
    {ι : Type*} [Countable ι] (f : ι → Lp ℝ 2 m) (b : ι → Lp ℝ 2 n)
    (habs : Summable fun i => ‖tensorLp (f i) (b i)‖)
    {Q : Lp ℝ 2 (m.prod n)} (hQ : HasSum (fun i => tensorLp (f i) (b i)) Q)
    (q : Lp ℝ 2 (m'.prod n'))
    (hslice : ∀ᵐ y ∂n', ∃ u : Lp ℝ 2 m', ((u : α → ℝ) =ᵐ[m'] fun x => q (x,y)) ∧
      HasSum (fun i => b i y • restrictL2 hm (f i)) u) :
    (Q : α × β → ℝ) =ᵐ[m'.prod n'] q := by
  have htsum := Lp.hasSum_coeFn_tsum (tsum_enorm_ne_top_iff_summable_norm.mpr habs)
  rw [hQ.tsum_eq] at htsum
  have hpoint : ∀ᵐ z ∂m'.prod n', HasSum (fun i => f i z.1 * b i z.2) (Q z) := by
    apply ae_mono (Measure.prod_mono hm hn)
    filter_upwards [htsum, ae_all_iff.mpr (fun i => tensorLp_ae (f i) (b i))] with z hz hz'
    simpa only [hz'] using hz
  have hpoint' := Measure.ae_ae_of_ae_prod
    ((Measure.measurePreserving_swap (μ := n') (ν := m')).quasiMeasurePreserving.ae hpoint)
  have hxy : ∀ᵐ y ∂n', ∀ᵐ x ∂m', Q (x,y) = q (x,y) := by
    filter_upwards [hpoint', hslice] with y hy hys
    obtain ⟨u, hu, hs⟩ := hys
    obtain ⟨s, hseq, hlim⟩ := (tendstoInMeasure_of_tendsto_Lp hs).exists_seq_tendsto_ae'
    have hfinite (k : ℕ) :
        ((∑ i ∈ s k, b i y • restrictL2 hm (f i) : Lp ℝ 2 m') : α → ℝ) =ᵐ[m']
          fun x => ∑ i ∈ s k, f i x * b i y := by
      have he (i : ι) : ((b i y • restrictL2 hm (f i) : Lp ℝ 2 m') : α → ℝ) =ᵐ[m']
          fun x => f i x * b i y := by
        filter_upwards [Lp.coeFn_smul (b i y) (restrictL2 hm (f i)), restrictL2_ae hm (f i)]
          with x hx hx'
        simp [hx, hx', mul_comm]
      filter_upwards [Lp.coeFn_fun_finsetSum (s k) (fun i => b i y • restrictL2 hm (f i)),
        ae_all_iff.mpr he] with x hx hx'
      rw [hx]
      exact Finset.sum_congr rfl (fun i _ => hx' i)
    filter_upwards [hy, hu, hlim, ae_all_iff.mpr hfinite] with x hx hux hl hf
    have hx' : HasSum (fun i => f i x * b i y) (Q (x,y)) := hx
    have hseqQ := hx'.comp hseq
    have hseqU : Tendsto (fun k => ∑ i ∈ s k, f i x * b i y) atTop (𝓝 (u x)) := by
      simpa only [hf] using hl
    exact (tendsto_nhds_unique hseqQ hseqU).trans hux
  have hyx : ∀ᵐ z ∂n'.prod m', Q z.swap = q z.swap := by
    apply (Measure.ae_prod_iff_ae_ae ?_).mpr hxy
    exact measurableSet_eq_fun ((Lp.stronglyMeasurable Q).measurable.comp measurable_swap)
      ((Lp.stronglyMeasurable q).measurable.comp measurable_swap)
  exact (Measure.measurePreserving_swap (μ := m') (ν := n')).quasiMeasurePreserving.ae hyx

end LocalMetricExtension
