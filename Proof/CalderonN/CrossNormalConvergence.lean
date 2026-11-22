module

public import Proof.CalderonN.CrossExtension
public import Proof.CalderonN.InteriorJetCutoff
public import Proof.CalderonN.GreenCross

import Proof.CalderonN.NormalTensorSeries
import Proof.CalderonN.EllipticCalculus
import Proof.CalderonN.GreenWeak
import Mathlib.MeasureTheory.Function.LpSpace.InfiniteSum
import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.Tactic

public section

noncomputable section
open Set Filter MeasureTheory
open scoped ContDiff ENNReal Topology

namespace CalderonN

variable {dim : ℕ} [NeZero dim]
open LocalMetricExtension

private theorem laplace_congr_germ (g : (MetricField dim)) {f h : (X dim) → ℝ} {p : (X dim)}
    (heq : f =ᶠ[𝓝 p] h) : laplace g f p = laplace g h p := by
  obtain ⟨U,hU,hUo,hp⟩ := eventually_nhds_iff.mp heq
  exact laplace_congrOn hUo (fun _ _ => rfl) hU hp

private theorem exists_point_cutoff {U : Set (X dim)} (hU : IsOpen U) {p : (X dim)} (hp : p ∈ U) :
    ∃ χ : (X dim) → ℝ, ContDiff ℝ ∞ χ ∧ HasCompactSupport χ ∧ tsupport χ ⊆ U ∧
      χ =ᶠ[𝓝 p] fun _ => (1 : ℝ) := by
  obtain ⟨χ,hχ,hχc,hχU,hχ₁⟩ := Elliptic.exists_plateau_cutoff
    hU (isCompact_singleton (x := p)) (singleton_subset_iff.mpr hp)
  exact ⟨χ,hχ,hχc,hχU,hχ₁ p (mem_singleton p)⟩

/-- Interior scalar derivative bounds upgrade the actual absolutely
convergent tensor series to a smooth product solution. -/
theorem exists_smooth_productSeries {D₁ D₂ : Set (X dim)}
    (hD₁ : IsOpen D₁) (hD₂ : IsOpen D₂)
    {g₁ g₂ : (MetricField dim)} (gD₁ : SmoothMetric D₁ g₁) (gD₂ : SmoothMetric D₂ g₂)
    (hjet₁ : HarmonicInteriorJets D₁ g₁) (hjet₂ : HarmonicInteriorJets D₂ g₂)
    {ι : Type*} [Countable ι]
    (f : ι → harmonicL2Space hD₁ gD₁) (b : ι → harmonicL2Space hD₂ gD₂)
    {Q : ChartProductL2 (d := dim) D₁ D₂} (habs : Summable fun i => ‖tensorLp (f i).1 (b i).1‖)
    (hQ : HasSum (fun i => tensorLp (f i).1 (b i).1) Q) :
    ∃ F : (X dim) × (X dim) → ℝ, ProductSolutionOn g₁ g₂ (D₁ ×ˢ D₂) F ∧
      (Q : (X dim) × (X dim) → ℝ) =ᵐ[((volume : Measure (X dim)).restrict D₁).prod
        ((volume : Measure (X dim)).restrict D₂)] F := by
  classical
  choose a ha haeq using fun i => harmonicL2Space_representative hD₁ gD₁ (f i)
  choose c hc hceq using fun i => harmonicL2Space_representative hD₂ gD₂ (b i)
  let F (q : (X dim) × (X dim)) := ∑' i, a i q.1 * c i q.2
  have hsum : Summable (fun i => ‖(f i).1‖ * ‖(b i).1‖) := by
    simpa only [norm_tensorLp] using habs
  refine ⟨F,?_,?_⟩
  · suffices hlocal : ∀ q ∈ D₁ ×ˢ D₂, ContDiffAt ℝ ∞ F q ∧
        laplace g₁ (fun x => F (x,q.2)) q.1 = 0 ∧
        laplace g₂ (fun y => F (q.1,y)) q.2 = 0 by
      exact ⟨fun q hq => (hlocal q hq).1.contDiffWithinAt,
        fun q hq => (hlocal q hq).2.1, fun q hq => (hlocal q hq).2.2⟩
    rintro ⟨x,y⟩ ⟨hx,hy⟩
    obtain ⟨χ,hχ,hχc,hχD,hχ₁⟩ := exists_point_cutoff hD₁ hx
    obtain ⟨ζ,hζ,hζc,hζD,hζ₁⟩ := exists_point_cutoff hD₂ hy
    let a' (i : ι) (q : (X dim)) := χ q * a i q
    let c' (i : ι) (q : (X dim)) := ζ q * c i q
    have ha' (i : ι) : ContDiff ℝ ∞ (a' i) :=
      Elliptic.contDiff_mul_of_tsupport_subset hD₁ hχ hχD (ha i).1
    have hc' (i : ι) : ContDiff ℝ ∞ (c' i) :=
      Elliptic.contDiff_mul_of_tsupport_subset hD₂ hζ hζD (hc i).1
    choose A hA hAb using exists_global_cutoff_jet_bound hD₁ hjet₁ hχ hχc hχD
    choose C hC hCb using exists_global_cutoff_jet_bound hD₂ hjet₂ hζ hζc hζD
    have hder₁ (k : ℕ) (i : ι) (p : (X dim)) : ‖iteratedFDeriv ℝ k (a' i) p‖ ≤ A k * ‖(f i).1‖ :=
      hAb k (f i).1 (a i) (ha i) (haeq i) p
    have hder₂ (k : ℕ) (i : ι) (p : (X dim)) : ‖iteratedFDeriv ℝ k (c' i) p‖ ≤ C k * ‖(b i).1‖ :=
      hCb k (b i).1 (c i) (hc i) (hceq i) p
    let J (p : (X dim) × (X dim)) := ∑' i, a' i p.1 * c' i p.2
    have hJ : ContDiff ℝ ∞ J := contDiff_tsum_tensor_of_global_jets
      ha' hc' (fun _ => norm_nonneg _) (fun _ => norm_nonneg _) hA hC hder₁ hder₂ hsum
    have hJa : J =ᶠ[𝓝 (x,y)] F := by
      filter_upwards [continuous_fst.continuousAt.preimage_mem_nhds hχ₁,
        continuous_snd.continuousAt.preimage_mem_nhds hζ₁] with p hp hp'
      simp only [Set.mem_preimage, Set.mem_ofPred_eq] at hp hp'
      simp [J,F,a',c',hp,hp']
    have hJa₁ : (fun p => J (p,y)) =ᶠ[𝓝 x] fun p => F (p,y) :=
      hJa.comp_tendsto (continuous_id.prodMk continuous_const).continuousAt
    have hJa₂ : (fun p => J (x,p)) =ᶠ[𝓝 y] fun p => F (x,p) :=
      hJa.comp_tendsto (continuous_const.prodMk continuous_id).continuousAt
    have hL₁ (i : ι) : laplace g₁ (a' i) x = 0 := by
      have h : a' i =ᶠ[𝓝 x] a i := by
        filter_upwards [hχ₁] with p hp
        simp [a',hp]
      exact (laplace_congr_germ g₁ h).trans ((ha i).2 x hx)
    have hL₂ (i : ι) : laplace g₂ (c' i) y = 0 := by
      have h : c' i =ᶠ[𝓝 y] c i := by
        filter_upwards [hζ₁] with p hp
        simp [c',hp]
      exact (laplace_congr_germ g₂ h).trans ((hc i).2 y hy)
    have hcs : Summable (fun i => ‖(f i).1‖ * (C 0 * ‖(b i).1‖)) := by
      convert hsum.mul_left (C 0) using 1
      funext i
      ring
    have has : Summable (fun i => ‖(b i).1‖ * (A 0 * ‖(f i).1‖)) := by
      convert hsum.mul_left (A 0) using 1
      funext i
      ring
    have hslice₁ := laplace_tsum_mul_eq_zero_of_global_jets ha' (fun _ => norm_nonneg _)
      (fun i => by simpa only [norm_iteratedFDeriv_zero] using hder₂ 0 i y) hA hder₁ hcs g₁ x hL₁
    have hslice₂ := laplace_tsum_mul_eq_zero_of_global_jets hc' (fun _ => norm_nonneg _)
      (fun i => by simpa only [norm_iteratedFDeriv_zero] using hder₁ 0 i x) hC hder₂ has g₂ y hL₂
    refine ⟨hJ.contDiffAt.congr_of_eventuallyEq hJa.symm,?_,?_⟩
    · rw [← laplace_congr_germ g₁ hJa₁]
      simpa [J,mul_comm] using hslice₁
    · rw [← laplace_congr_germ g₂ hJa₂]
      exact hslice₂
  · let μ := (volume : Measure (X dim)).restrict D₁
    let ν := (volume : Measure (X dim)).restrict D₂
    have htsum := Lp.hasSum_coeFn_tsum (tsum_enorm_ne_top_iff_summable_norm.mpr habs)
    rw [hQ.tsum_eq] at htsum
    have hf' (i : ι) : ∀ᵐ q ∂μ.prod ν, (f i).1 q.1 = a i q.1 :=
      Measure.quasiMeasurePreserving_fst.ae (haeq i)
    have hb' (i : ι) : ∀ᵐ q ∂μ.prod ν, (b i).1 q.2 = c i q.2 :=
      Measure.quasiMeasurePreserving_snd.ae (hceq i)
    filter_upwards [htsum, ae_all_iff.mpr hf', ae_all_iff.mpr hb',
      ae_all_iff.mpr (fun i => tensorLp_ae (f i).1 (b i).1)] with q hsum hfa hbc htt
    have hs : HasSum (fun i => a i q.1 * c i q.2) (Q q) := by
      simpa only [htt,hfa,hbc] using hsum
    exact hs.tsum_eq.symm

end CalderonN
