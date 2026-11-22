module

public import Proof.CalderonN.TransferReproduction

import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.Tactic

/-! Adapted from `EnlargedTraceDensity` in the checked Theorem 3.1 release. -/

public section

set_option maxHeartbeats 2400000

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal ContDiff

namespace CalderonN

variable {dim : ℕ} [NeZero dim] [Nontrivial (Fin dim)]

private theorem sphereProbability_openPos : (sphereProbability dim).IsOpenPosMeasure := by
  let μ := (volume : Measure (X dim)).toSphere
  have hμ : μ univ ≠ 0 := by
    rw [ne_eq,Measure.measure_univ_eq_zero]
    exact Measure.toSphere_ne_zero _
  show (((μ univ)⁻¹) • μ).IsOpenPosMeasure
  exact Measure.isOpenPosMeasure_smul μ (by simp [measure_ne_top μ univ])

/-- A continuous angular function is zero when all traces from slightly
enlarged balls annihilate it and a continuous radius family approaches
its own boundary data. This uses the trace at radius zero only as a
limit. -/
theorem eq_zero_of_annihilates_enlarged_trace_family
    {a : ↥(standardSphere dim) → ℝ} (ha : Continuous a)
    {ε : ℝ} (hε : 0 < ε)
    (b : ℝ × ↥(standardSphere dim) → ℝ)
    (hb : ContinuousOn b (Icc (0 : ℝ) ε ×ˢ (univ : Set ↥(standardSphere dim))))
    (hzero : ∀ w, b (0,w) = a w)
    (hann : ∀ t ∈ Ioc (0 : ℝ) ε, ∫ w, a w * b (t,w) ∂(sphereProbability dim) = 0) :
    a = 0 := by
  let : CompactSpace ↥(standardSphere dim) :=
    isCompact_iff_compactSpace.mp (isCompact_sphere (0 : (X dim)) 1)
  let : (sphereProbability dim).IsOpenPosMeasure := sphereProbability_openPos
  let P (q : ℝ × ↥(standardSphere dim)) := a q.2 * b q
  let L : Filter ℝ := 𝓝[Set.Ioi (0 : ℝ)] 0
  have hP : ContinuousOn P (Icc 0 ε ×ˢ (univ : Set ↥(standardSphere dim))) :=
    (ha.comp continuous_snd).continuousOn.mul hb
  obtain ⟨B,hB⟩ := (isCompact_Icc.prod isCompact_univ).exists_bound_of_continuousOn hP
  have ht : ∀ᶠ t in L, t ∈ Ioc (0 : ℝ) ε := by
    have hlt : ∀ᶠ t in 𝓝 (0 : ℝ), t < ε := Iio_mem_nhds hε
    have hlt' : ∀ᶠ t in L, t < ε := hlt.filter_mono nhdsWithin_le_nhds
    have hpos : ∀ᶠ t in L, 0 < t := self_mem_nhdsWithin
    exact (hpos.and hlt').mono (fun _ h => ⟨h.1,h.2.le⟩)
  have hInt : Tendsto (fun t => ∫ w, P (t,w) ∂(sphereProbability dim)) L
      (𝓝 (∫ w, a w ^ 2 ∂(sphereProbability dim))) := by
    apply tendsto_integral_filter_of_dominated_convergence (bound := fun _ => B)
    · filter_upwards [ht] with t ht
      have hp : Continuous (fun w => P (t,w)) :=
        hP.comp_continuous (continuous_const.prodMk continuous_id) (fun w => ⟨⟨ht.1.le,ht.2⟩,mem_univ w⟩)
      exact hp.aestronglyMeasurable
    · filter_upwards [ht] with t ht
      exact ae_of_all _ (fun w => hB (t,w) ⟨⟨ht.1.le,ht.2⟩,mem_univ w⟩)
    · exact integrable_const B
    · apply ae_of_all _
      intro w
      have hmap : Tendsto (fun t : ℝ => (t,w)) L
          (𝓝[Icc (0 : ℝ) ε ×ˢ (univ : Set ↥(standardSphere dim))] (0,w)) := by
        apply tendsto_nhdsWithin_iff.mpr
        refine ⟨(continuous_id.prodMk continuous_const).continuousAt.tendsto.mono_left nhdsWithin_le_nhds, ?_⟩
        exact ht.mono (fun t ht => ⟨⟨ht.1.le,ht.2⟩,mem_univ w⟩)
      have h := (hP (0,w) ⟨⟨le_rfl,hε.le⟩,mem_univ w⟩).tendsto.comp hmap
      change Tendsto (fun t => P (t,w)) L (𝓝 (P (0,w))) at h
      simpa only [P, hzero w, pow_two] using h
  have h0 : (fun t => ∫ w, P (t,w) ∂(sphereProbability dim)) =ᶠ[L] fun _ => (0 : ℝ) :=
    ht.mono (fun t ht => hann t ht)
  have hZ : ∫ w, a w^2 ∂(sphereProbability dim) = 0 :=
    tendsto_nhds_unique hInt (tendsto_const_nhds.congr' h0.symm)
  have hI : Integrable (fun w => a w^2) (sphereProbability dim) :=
    (ha.pow 2).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have he := (integral_eq_zero_iff_of_nonneg (fun w => sq_nonneg (a w)) hI).mp hZ
  have hae : a =ᵐ[(sphereProbability dim)] fun _ => (0 : ℝ) := by
    filter_upwards [he] with w hw
    exact sq_eq_zero_iff.mp hw
  ext w
  have hpoint := Measure.eqOn_open_of_ae_eq (μ := (sphereProbability dim))
    (by simpa using hae) isOpen_univ ha.continuousOn continuousOn_const
  exact hpoint (mem_univ w)

/-- The same density is uniquely determined by testing real traces on
enlarged balls. The radius families for the real and imaginary parts can
be chosen independently. -/
theorem complex_eq_zero_of_enlarged_trace_duality
    {v : ↥(standardSphere dim) → ℂ} (hv : Continuous v) {ε : ℝ} (hε : 0 < ε)
    (b c : ℝ × ↥(standardSphere dim) → ℝ)
    (hb : ContinuousOn b (Icc (0 : ℝ) ε ×ˢ (univ : Set ↥(standardSphere dim))))
    (hc : ContinuousOn c (Icc (0 : ℝ) ε ×ˢ (univ : Set ↥(standardSphere dim))))
    (hb₀ : ∀ w, b (0,w) = (v w).re) (hc₀ : ∀ w, c (0,w) = (v w).im)
    (hB : ∀ t ∈ Ioc (0 : ℝ) ε, ∫ w, v w * (b (t,w) : ℂ) ∂(sphereProbability dim) = 0)
    (hC : ∀ t ∈ Ioc (0 : ℝ) ε, ∫ w, v w * (c (t,w) : ℂ) ∂(sphereProbability dim) = 0) :
    v = 0 := by
  let : CompactSpace ↥(standardSphere dim) :=
    isCompact_iff_compactSpace.mp (isCompact_sphere (0 : (X dim)) 1)
  have hbi (t : ℝ) (ht : t ∈ Ioc (0 : ℝ) ε) :
      Integrable (fun w => v w * (b (t,w) : ℂ)) (sphereProbability dim) := by
    have hcont : Continuous (fun w => b (t,w)) :=
      hb.comp_continuous (continuous_const.prodMk continuous_id) (fun w => ⟨⟨ht.1.le,ht.2⟩,mem_univ w⟩)
    exact (hv.mul (Complex.continuous_ofReal.comp hcont)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hci (t : ℝ) (ht : t ∈ Ioc (0 : ℝ) ε) :
      Integrable (fun w => v w * (c (t,w) : ℂ)) (sphereProbability dim) := by
    have hcont : Continuous (fun w => c (t,w)) :=
      hc.comp_continuous (continuous_const.prodMk continuous_id) (fun w => ⟨⟨ht.1.le,ht.2⟩,mem_univ w⟩)
    exact (hv.mul (Complex.continuous_ofReal.comp hcont)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hre := eq_zero_of_annihilates_enlarged_trace_family (Complex.continuous_re.comp hv) hε b hb hb₀
    (fun t ht => by
      have h := congrArg (RCLike.re : ℂ → ℝ) (hB t ht)
      rw [← integral_re (hbi t ht)] at h
      change (∫ w, (v w * (b (t,w) : ℂ)).re ∂(sphereProbability dim)) = (0 : ℂ).re at h
      simpa only [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,mul_zero,sub_zero,
        Complex.zero_re,Function.comp_apply] using h)
  have him := eq_zero_of_annihilates_enlarged_trace_family (Complex.continuous_im.comp hv) hε c hc hc₀
    (fun t ht => by
      have h := congrArg (RCLike.im : ℂ → ℝ) (hC t ht)
      rw [← integral_im (hci t ht)] at h
      change (∫ w, (v w * (c (t,w) : ℂ)).im ∂(sphereProbability dim)) = (0 : ℂ).im at h
      simpa only [Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,mul_zero,zero_add,
        Complex.zero_im,Function.comp_apply] using h)
  funext w
  exact Complex.ext (congrFun hre w) (congrFun him w)

end CalderonN
