module

public import Proof.CalderonN.NormalFluxDensity

import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Tactic

public section

noncomputable section

open Set Metric Filter MeasureTheory CalderonN
open scoped ContDiff ENNReal Topology

namespace CalderonPaper.LowerGreen

variable {n : ℕ} [NeZero n]

theorem sphereDensity_eq_of_smooth_pairings
    {u v : ↥(standardSphere n) → ℝ} (hu : Continuous u) (hv : Continuous v)
    (h : ∀ a : X n → ℝ, ContDiff ℝ ∞ a →
      (∫ w, u w * a w ∂sphereProbability n) = ∫ w, v w * a w ∂sphereProbability n) :
    u = v := by
  let S := ↥(standardSphere n)
  let μ := sphereProbability n
  let : CompactSpace S := isCompact_iff_compactSpace.mp (isCompact_sphere (0 : X n) 1)
  let : μ.IsOpenPosMeasure := by
    let σ := (volume : Measure (X n)).toSphere
    have h0 : σ univ ≠ 0 := by rw [ne_eq,Measure.measure_univ_eq_zero]; exact Measure.toSphere_ne_zero _
    change (((σ univ)⁻¹) • σ).IsOpenPosMeasure
    exact Measure.isOpenPosMeasure_smul σ (by simp [measure_ne_top σ univ])
  have hPos (f : S → ℝ) (hf : Continuous f)
      (hAnn : ∀ a : X n → ℝ, ContDiff ℝ ∞ a →
        (∫ w : S, f w * a w ∂μ) = 0) (w₀ : S) : f w₀ ≤ 0 := by
    by_contra! h₀
    let U := {w : S | 0 < f w}
    have hU : IsOpen U := isOpen_lt continuous_const hf
    obtain ⟨V,hV,hUV⟩ := isOpen_induced_iff.mp hU
    have hwV : (w₀ : X n) ∈ V := by
      change w₀ ∈ Subtype.val ⁻¹' V
      rw [hUV]
      exact h₀
    obtain ⟨d,hd,hdV⟩ := Metric.isOpen_iff.mp hV w₀ hwV
    let b : ContDiffBump (w₀ : X n) := ⟨d/2,d,half_pos hd,half_lt_self hd⟩
    have hb : ContDiff ℝ ∞ (b : X n → ℝ) := b.contDiff
    have hw (w : S) (hwb : b w ≠ 0) : w ∈ U := by
      rw [← hUV]
      apply hdV
      exact b.support_eq ▸ hwb
    let F (w : S) := f w * b w
    have hF₀ : 0 ≤ F := by
      intro w
      by_cases hwb : b w = 0
      · simp [F,hwb]
      · exact mul_nonneg (le_of_lt (hw w hwb)) (b.nonneg)
    have hF : Continuous F := hf.mul (hb.continuous.comp continuous_subtype_val)
    have hFInt : Integrable F μ := hF.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
    have hFpos : 0 < F w₀ := by
      change 0 < f w₀ * b w₀
      rw [b.one_of_mem_closedBall (mem_closedBall_self (half_pos hd).le),mul_one]
      exact h₀
    have hSupp : IsOpen (Function.support F) := hF.isOpen_support
    have hμ : 0 < μ (Function.support F) := hSupp.measure_pos μ ⟨w₀,hFpos.ne'⟩
    exact (ne_of_gt ((integral_pos_iff_support_of_nonneg hF₀ hFInt).mpr hμ)) (hAnn b hb)
  have hAnn (f g : S → ℝ) (hf : Continuous f) (hg : Continuous g)
      (he : ∀ a : X n → ℝ, ContDiff ℝ ∞ a →
        ∫ w : S, f w * a w ∂μ = ∫ w : S, g w * a w ∂μ)
      (a : X n → ℝ) (ha : ContDiff ℝ ∞ a) :
      ∫ w : S, (f w-g w) * a w ∂μ = 0 := by
    have hfI : Integrable (fun w : S => f w * a w) μ :=
      (hf.mul (ha.continuous.comp continuous_subtype_val)).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)
    have hgI : Integrable (fun w : S => g w * a w) μ :=
      (hg.mul (ha.continuous.comp continuous_subtype_val)).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)
    simpa only [Pi.sub_apply,sub_mul,he a ha,sub_self] using integral_sub hfI hgI
  funext w
  exact le_antisymm (sub_nonpos.mp (hPos (u-v) (hu.sub hv) (hAnn u v hu hv h) w))
    (sub_nonpos.mp (hPos (v-u) (hv.sub hu) (hAnn v u hv hu (fun a ha => (h a ha).symm)) w))

/-- Test an enlarged trace at positive enlargement and then take its
continuous boundary limit at enlargement zero. -/
theorem spherePair_eq_at_zero_of_positive
    {u v : ↥(standardSphere n) → ℝ} (hu : Continuous u) (hv : Continuous v)
    {ε : ℝ} (hε : 0 < ε) {b : ℝ × ↥(standardSphere n) → ℝ}
    (hb : ContinuousOn b (Icc (0 : ℝ) ε ×ˢ (univ : Set ↥(standardSphere n))))
    (h : ∀ t ∈ Ioc (0 : ℝ) ε,
      (∫ w, u w * b (t,w) ∂sphereProbability n) = ∫ w, v w * b (t,w) ∂sphereProbability n) :
    (∫ w, u w * b (0,w) ∂sphereProbability n) = ∫ w, v w * b (0,w) ∂sphereProbability n := by
  let J := Icc 0 ε
  let T := ↥(standardSphere n)
  let : CompactSpace T := isCompact_iff_compactSpace.mp (isCompact_sphere (0 : X n) 1)
  let L : Filter ℝ := 𝓝[Ioi (0 : ℝ)] 0
  have ht : ∀ᶠ t in L, t ∈ Ioc (0 : ℝ) ε := by
    have hlt : ∀ᶠ t in 𝓝 (0 : ℝ), t < ε := Iio_mem_nhds hε
    have hlt' : ∀ᶠ t in L, t < ε := hlt.filter_mono nhdsWithin_le_nhds
    have hpos : ∀ᶠ t in L, 0 < t := self_mem_nhdsWithin
    exact (hpos.and hlt').mono (fun _ h => ⟨h.1,h.2.le⟩)
  have hLim (a : T → ℝ) (ha : Continuous a) :
      Tendsto (fun t => ∫ w, a w * b (t,w) ∂sphereProbability n) L
        (𝓝 (∫ w, a w * b (0,w) ∂sphereProbability n)) := by
    let H (p : ℝ × T) := a p.2 * b p
    have hH : ContinuousOn H (J ×ˢ (univ : Set T)) :=
      (ha.comp continuous_snd).continuousOn.mul hb
    obtain ⟨B,hB⟩ := (isCompact_Icc.prod isCompact_univ).exists_bound_of_continuousOn hH
    apply tendsto_integral_filter_of_dominated_convergence (bound := fun _ => B)
    · filter_upwards [ht] with t ht
      exact (hH.comp_continuous (continuous_const.prodMk continuous_id)
        (fun w => ⟨⟨ht.1.le,ht.2⟩,mem_univ w⟩)).aestronglyMeasurable
    · filter_upwards [ht] with t ht
      exact ae_of_all _ (fun w => hB (t,w) ⟨⟨ht.1.le,ht.2⟩,mem_univ w⟩)
    · exact integrable_const B
    · apply ae_of_all _
      intro w
      have hmap : Tendsto (fun t : ℝ => (t,w)) L (𝓝[J ×ˢ (univ : Set T)] (0,w)) := by
        apply tendsto_nhdsWithin_iff.mpr
        refine ⟨(continuous_id.prodMk continuous_const).continuousAt.tendsto.mono_left
          nhdsWithin_le_nhds,ht.mono (fun _ ht => ⟨⟨ht.1.le,ht.2⟩,mem_univ w⟩)⟩
      exact (hH (0,w) ⟨⟨le_rfl,hε.le⟩,mem_univ w⟩).tendsto.comp hmap
  have he : (fun t => ∫ w, u w * b (t,w) ∂sphereProbability n) =ᶠ[L]
      (fun t => ∫ w, v w * b (t,w) ∂sphereProbability n) := ht.mono h
  exact tendsto_nhds_unique (hLim u hu) ((hLim v hv).congr' he.symm)

end CalderonPaper.LowerGreen

end
