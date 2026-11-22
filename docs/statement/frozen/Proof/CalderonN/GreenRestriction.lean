module

public import Proof.CalderonN.Chart
public import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
public import Mathlib.Geometry.Manifold.IsManifold.InteriorBoundary
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

import Mathlib.Topology.Instances.Matrix
import Proof.CalderonN.ChartGeometry

@[expose] public section

noncomputable section
open Set Filter MeasureTheory
open scoped ContDiff ENNReal Manifold Topology

namespace CalderonN

variable {n : ℕ} {H M : Type*} [TopologicalSpace H] [TopologicalSpace M]
  [ChartedSpace H M] {J : ModelWithCorners ℝ (X n) H}

/-- Extend a compactly supported coordinate test by zero off the chart source. -/
def chartTest (e : OpenPartialHomeomorph M (X n)) (u : X n → ℝ) : M → ℝ :=
  e.source.indicator (u ∘ e)

theorem tsupport_chartTest_subset [T2Space M] (e : OpenPartialHomeomorph M (X n)) {u : X n → ℝ}
    (hu : HasCompactSupport u) (hus : tsupport u ⊆ e.target) :
    tsupport (chartTest e u) ⊆ e.symm '' tsupport u := by
  have hcomp : IsCompact (e.symm '' tsupport u) :=
    hu.image_of_continuousOn (e.symm.continuousOn.mono hus)
  apply closure_minimal _ hcomp.isClosed
  intro p hp
  have hens : p ∈ e.source := by
    by_contra hout
    exact hp (indicator_of_notMem hout _)
  refine ⟨e p, subset_tsupport _ ?_, e.left_inv hens⟩
  change chartTest e u p ≠ 0 at hp
  change u (e p) ≠ 0
  simpa only [chartTest, indicator_of_mem hens, Function.comp_apply] using hp

theorem hasCompactSupport_chartTest [T2Space M] (e : OpenPartialHomeomorph M (X n)) {u : X n → ℝ}
    (hu : HasCompactSupport u) (hus : tsupport u ⊆ e.target) :
    HasCompactSupport (chartTest e u) :=
  (hu.image_of_continuousOn (e.symm.continuousOn.mono hus)).of_isClosed_subset
    isClosed_closure (tsupport_chartTest_subset e hu hus)

theorem contMDiff_chartTest [T2Space M] (e : OpenPartialHomeomorph M (X n))
    (he : ContMDiffOn J 𝓘(ℝ, X n) ∞ e e.source) {u : X n → ℝ}
    (hu : ContDiff ℝ ∞ u) (huc : HasCompactSupport u) (hus : tsupport u ⊆ e.target) :
    ContMDiff J 𝓘(ℝ, ℝ) ∞ (chartTest e u) := by
  intro p
  by_cases hp : p ∈ e.source
  · have h := (hu.contMDiff.contMDiffAt.comp p (he.contMDiffAt (e.open_source.mem_nhds hp)))
    apply h.congr_of_eventuallyEq
    filter_upwards [e.open_source.mem_nhds hp] with q hq
    exact indicator_of_mem hq _
  · have hs : p ∉ tsupport (chartTest e u) := by
      intro hsupport
      obtain ⟨x, hx, rfl⟩ := tsupport_chartTest_subset e huc hus hsupport
      exact hp (e.map_target (hus hx))
    apply (show ContMDiffAt J 𝓘(ℝ, ℝ) ∞ (fun _ : M => (0 : ℝ)) p from
      contMDiffAt_const).congr_of_eventuallyEq
    filter_upwards [isClosed_closure.isOpen_compl.mem_nhds hs] with q hq
    exact image_eq_zero_of_notMem_tsupport hq

/-- The coordinate density for Riemannian volume on an interior chart. -/
def chartVolumeMeasure (Ω : Set (X n)) (g : MetricField n) : Measure (X n) :=
  (volume.restrict Ω).withDensity (fun x => ENNReal.ofReal (Real.sqrt (g x).det))

theorem continuousOn_metricVolumeDensity {Ω : Set (X n)} {g : MetricField n}
    (hg : SmoothMetric Ω g) : ContinuousOn (fun x => Real.sqrt (g x).det) Ω := by
  have hdet : ContinuousOn (fun x => (g x).det) Ω := by
    rw [continuousOn_iff_continuous_domRestrict]
    have hmatrix : Continuous (fun x : Ω => g x) :=
      continuous_pi fun i => continuous_pi fun j =>
        continuousOn_iff_continuous_domRestrict.mp (hg.1 i j).continuousOn
    exact hmatrix.matrix_det
  exact hdet.sqrt

theorem integral_chartVolume {Ω : Set (X n)} (hΩ : IsOpen Ω) (g : MetricField n)
    (hg : SmoothMetric Ω g) (f : X n → ℝ) :
    (∫ x, f x ∂chartVolumeMeasure Ω g) = ∫ x in Ω, f x * Real.sqrt (g x).det := by
  have hmeas := (continuousOn_metricVolumeDensity hg).aemeasurable hΩ.measurableSet
    (μ := (volume : Measure (X n)))
  unfold chartVolumeMeasure
  rw [integral_withDensity_eq_integral_toReal_smul₀ hmeas.ennreal_ofReal
    (ae_of_all _ (fun _ => ENNReal.ofReal_lt_top)) f]
  simp only [ENNReal.toReal_ofReal (Real.sqrt_nonneg _), smul_eq_mul, mul_comm]

/-- Transport the global distributional pairing for an extended chart test.
The chart identities here are those of the Riemannian volume and Laplacian. -/
theorem integral_green_chartTest
    [MeasurableSpace M] [BorelSpace M]
    (e : OpenPartialHomeomorph M (X n)) (g : MetricField n) (hg : SmoothMetric e.target g)
    (μ : Measure M) (hμ : (μ.restrict e.source).map e = chartVolumeMeasure e.target g)
    (G : M × M → ℝ) (L : (M → ℝ) → M → ℝ) (u : X n → ℝ)
    (y : X n)
    (hLap : ∀ p ∈ e.source, L (chartTest e u) p = laplace g u (e p))
    (hzero : ∀ p ∉ e.source, L (chartTest e u) p = 0)
    (hF : AEStronglyMeasurable
      (fun x => G (e.symm x, e.symm y) * (-laplace g u x)) (chartVolumeMeasure e.target g)) :
    (∫ p, G (p, e.symm y) * (-L (chartTest e u) p) ∂μ) =
      ∫ x in e.target, G (e.symm x, e.symm y) * (-laplace g u x) *
        Real.sqrt (g x).det := by
  let F : X n → ℝ := fun x => G (e.symm x, e.symm y) * (-laplace g u x)
  have he : AEMeasurable (e : M → X n) (μ.restrict e.source) :=
    e.continuousOn.aemeasurable e.open_source.measurableSet
  calc
    _ = ∫ p in e.source, G (p, e.symm y) * (-L (chartTest e u) p) ∂μ := by
      rw [← integral_indicator e.open_source.measurableSet]
      apply integral_congr_ae
      filter_upwards with p
      by_cases hp : p ∈ e.source
      · rw [indicator_of_mem hp]
      · simp [indicator_of_notMem hp, hzero p hp]
    _ = ∫ p in e.source, F (e p) ∂μ := by
      apply setIntegral_congr_fun e.open_source.measurableSet
      intro p hp
      simp only [F, e.left_inv hp, hLap p hp]
    _ = ∫ x, F x ∂chartVolumeMeasure e.target g := by
      rw [← hμ, integral_map he]
      exact hμ ▸ hF
    _ = _ := integral_chartVolume e.open_target g hg F

/-- A smooth positive metric density can be removed on compact subsets of the chart. -/
theorem locallyIntegrableOn_of_integrable_chartVolume {Ω : Set (X n)} (hΩ : IsOpen Ω)
    {g : MetricField n} (hg : SmoothMetric Ω g) {f : X n → ℝ}
    (hf : Integrable f (chartVolumeMeasure Ω g)) : LocallyIntegrableOn f Ω := by
  apply (locallyIntegrableOn_iff hΩ.isLocallyClosed).mpr
  intro K hKΩ hK
  by_cases hempty : K = ∅
  · rw [hempty]
    exact integrableOn_empty
  let d : X n → ℝ := fun x => Real.sqrt (g x).det
  have hd : ContinuousOn d K := (continuousOn_metricVolumeDensity hg).mono hKΩ
  have hpos : ∀ x ∈ K, 0 < d x := fun x hx => Real.sqrt_pos.2 (hg.2 x (hKΩ hx)).det_pos
  obtain ⟨z, hz, hmin⟩ := hK.exists_isMinOn (Set.nonempty_iff_ne_empty.mpr hempty) hd
  have hfd : Integrable (fun x => d x * f x) (volume.restrict K) := by
    have hden := hd.aemeasurable hK.measurableSet (μ := (volume : Measure (X n)))
    have hrest := hf.integrableOn (s := K)
    unfold chartVolumeMeasure at hrest
    rw [IntegrableOn, restrict_withDensity hK.measurableSet,
      Measure.restrict_restrict_of_subset hKΩ] at hrest
    have := (integrable_withDensity_iff_integrable_smul₀' hden.ennreal_ofReal
      (ae_of_all _ (fun _ => ENNReal.ofReal_lt_top))).mp hrest
    simpa only [ENNReal.toReal_ofReal (Real.sqrt_nonneg _), smul_eq_mul, d] using this
  have hinv : AEStronglyMeasurable (fun x => (d x)⁻¹) (volume.restrict K) :=
    ((hd.inv₀ (fun x hx => (hpos x hx).ne')).aemeasurable hK.measurableSet).aestronglyMeasurable
  have hbound : ∀ᵐ x ∂volume.restrict K, ‖(d x)⁻¹‖ ≤ (d z)⁻¹ := by
    filter_upwards [ae_restrict_mem hK.measurableSet] with x hx
    rw [Real.norm_eq_abs, abs_of_pos (inv_pos.2 (hpos x hx))]
    exact (inv_le_inv₀ (hpos x hx) (hpos z hz)).2 (hmin hx)
  refine (hfd.bdd_mul hinv hbound).congr ?_
  filter_upwards [ae_restrict_mem hK.measurableSet] with x hx
  exact (inv_mul_cancel_left₀ (hpos x hx).ne' (f x))

section Kernel

variable [MeasurableSpace M] [BorelSpace M] [T2Space M]

/-- The global properties of a supplied Dirichlet Green kernel for the inverse of
−L. The weak law is tested against smooth compactly supported interior functions. -/
structure IsDirichletGreenKernel (J : ModelWithCorners ℝ (X n) H) (μ : Measure M)
    (L : (M → ℝ) → M → ℝ) (G : M × M → ℝ) : Prop where
  smooth_off_diagonal : ContMDiffOn (J.prod J) 𝓘(ℝ, ℝ) ∞ G
    {p | p.1 ∈ J.interior M ∧ p.2 ∈ J.interior M ∧ p.1 ≠ p.2}
  symmetric : ∀ p q, p ∈ J.interior M → q ∈ J.interior M → p ≠ q → G (p, q) = G (q, p)
  continuous_off_pole : ∀ q ∈ J.interior M, ContinuousOn (fun p => G (p, q)) ({q}ᶜ)
  zero_on_boundary : ∀ p ∈ J.boundary M, ∀ q ∈ J.interior M, G (p, q) = 0
  integrable : ∀ q ∈ J.interior M, Integrable (fun p => G (p, q)) μ
  weak_inverse : ∀ q ∈ J.interior M, ∀ u : M → ℝ, ContMDiff J 𝓘(ℝ, ℝ) ∞ u →
    HasCompactSupport u → tsupport u ⊆ J.interior M →
    Integrable (fun p => G (p, q) * (-L u p)) μ ∧
      (∫ p, G (p, q) * (-L u p) ∂μ) = u q

/-- The coordinate realization of the metric, volume and differential operator
on one interior chart. -/
structure InteriorMetricChart (J : ModelWithCorners ℝ (X n) H) (μ : Measure M)
    (L : (M → ℝ) → M → ℝ) where
  chart : OpenPartialHomeomorph M (X n)
  source_interior : chart.source ⊆ J.interior M
  smooth : ContMDiffOn J 𝓘(ℝ, X n) ∞ chart chart.source
  smooth_inverse : ContMDiffOn 𝓘(ℝ, X n) J ∞ chart.symm chart.target
  metric : MetricField n
  smooth_metric : SmoothMetric chart.target metric
  volume_eq : (μ.restrict chart.source).map chart = chartVolumeMeasure chart.target metric
  laplace_eq : ∀ u : M → ℝ, ContMDiff J 𝓘(ℝ, ℝ) ∞ u →
    ∀ p ∈ chart.source, L u p = laplace metric (u ∘ chart.symm) (chart p)

private theorem chartVolume_absolutelyContinuous (Ω : Set (X n)) (g : MetricField n) :
    chartVolumeMeasure Ω g ≪ volume.restrict Ω :=
  withDensity_absolutelyContinuous _ _

omit [T2Space M] in
private theorem integrable_comp_chart_inverse (e : OpenPartialHomeomorph M (X n))
    (g : MetricField n) {μ : Measure M}
    (hμ : (μ.restrict e.source).map e = chartVolumeMeasure e.target g)
    {f : M → ℝ} (hf : Integrable f μ) :
    Integrable (f ∘ e.symm) (chartVolumeMeasure e.target g) := by
  have he : AEMeasurable (e : M → X n) (μ.restrict e.source) :=
    e.continuousOn.aemeasurable e.open_source.measurableSet
  have hinv : AEMeasurable (e.symm : X n → M) (chartVolumeMeasure e.target g) :=
    (e.symm.continuousOn.aemeasurable e.open_target.measurableSet).mono_ac
      (chartVolume_absolutelyContinuous e.target g)
  have hmap : (chartVolumeMeasure e.target g).map e.symm = μ.restrict e.source := by
    rw [← hμ, AEMeasurable.map_map_of_aemeasurable (hμ ▸ hinv) he]
    calc
      _ = (μ.restrict e.source).map id := by
        apply Measure.map_congr
        filter_upwards [ae_restrict_mem e.open_source.measurableSet] with p hp
        exact e.left_inv hp
      _ = _ := Measure.map_id
  have hf' : Integrable f ((chartVolumeMeasure e.target g).map e.symm) := hmap ▸ hf.integrableOn
  exact hf'.comp_aemeasurable hinv

set_option maxHeartbeats 600000 in
/-- Restrict an ambient weak Dirichlet Green kernel to the given interior chart. -/
theorem GreenGerm.of_dirichletKernel {μ : Measure M} {L : (M → ℝ) → M → ℝ}
    (C : InteriorMetricChart J μ L)
    (hloc : ∀ v : M → ℝ, ContMDiff J 𝓘(ℝ, ℝ) ∞ v → tsupport (L v) ⊆ tsupport v)
    {G : M × M → ℝ} (hG : IsDirichletGreenKernel J μ L G) :
    GreenGerm C.chart.target C.metric (fun p => G (C.chart.symm p.1, C.chart.symm p.2)) := by
  let e := C.chart
  have mapped : ∀ x ∈ e.target, e.symm x ∈ J.interior M :=
    fun x hx => C.source_interior (e.map_target hx)
  have hmaps : MapsTo (Prod.map e.symm e.symm) (OffDiagonal e.target)
      {p : M × M | p.1 ∈ J.interior M ∧ p.2 ∈ J.interior M ∧ p.1 ≠ p.2} := by
    intro p hp
    refine ⟨mapped p.1 hp.1, mapped p.2 hp.2.1, ?_⟩
    exact fun he => hp.2.2 (e.symm.injOn hp.1 hp.2.1 he)
  refine ⟨?_, ?_, ?_⟩
  · have hsm := (C.smooth_inverse.prodMap C.smooth_inverse).mono
      (show OffDiagonal e.target ⊆ e.target ×ˢ e.target from
        fun p hp => ⟨hp.1, hp.2.1⟩)
    have hs := hG.smooth_off_diagonal.comp hsm hmaps
    rw [← modelWithCornersSelf_prod, chartedSpaceSelf_prod] at hs
    exact hs.contDiffOn
  · intro p hp
    have h := hmaps hp
    exact hG.symmetric _ _ h.1 h.2.1 h.2.2
  · intro y hy
    have hy' := mapped y hy
    have hi := integrable_comp_chart_inverse e C.metric C.volume_eq
      (f := fun p => G (p, e.symm y)) (hG.integrable (e.symm y) hy')
    have hlocInt := locallyIntegrableOn_of_integrable_chartVolume e.open_target C.smooth_metric hi
    refine ⟨hlocInt, ?_⟩
    intro u hu huc hus
    let v := chartTest e u
    have hv : ContMDiff J 𝓘(ℝ, ℝ) ∞ v := contMDiff_chartTest e C.smooth hu huc hus
    have hvs : tsupport v ⊆ e.source :=
      (tsupport_chartTest_subset e huc hus).trans
        (fun _ ⟨x, hx, he⟩ => he ▸ e.map_target (hus hx))
    have hglob := hG.weak_inverse _ hy' v hv (hasCompactSupport_chartTest e huc hus)
      (hvs.trans C.source_interior)
    have hvu : EqOn (v ∘ e.symm) u e.target := by
      intro x hx
      simp only [v, chartTest, Function.comp_apply, indicator_of_mem (e.map_target hx),
        e.right_inv hx]
    have hLap : ∀ p ∈ e.source, L v p = laplace C.metric u (e p) := by
      intro p hp
      rw [C.laplace_eq v hv p hp]
      change laplace C.metric (v ∘ e.symm) (e p) = laplace C.metric u (e p)
      have hx := e.map_source hp
      have hfirst (i : I n) := eqOn_coordDeriv e.open_target hvu i hx
      have hsecond (i j : I n) :=
        eqOn_coordDeriv e.open_target (eqOn_coordDeriv e.open_target hvu j) i hx
      simp only [laplace, hfirst, hsecond]
    have hzero : ∀ p ∉ e.source, L v p = 0 := by
      intro p hp
      exact image_eq_zero_of_notMem_tsupport (fun h => hp (hvs (hloc v hv h)))
    have hFi := integrable_comp_chart_inverse e C.metric C.volume_eq
      (f := fun p => G (p, e.symm y) * (-L v p)) hglob.1
    have hF : AEStronglyMeasurable
        (fun x => G (e.symm x, e.symm y) * (-laplace C.metric u x))
        (chartVolumeMeasure e.target C.metric) := by
      apply hFi.aestronglyMeasurable.congr
      have hae := (chartVolume_absolutelyContinuous e.target C.metric).ae_le
        (ae_restrict_mem e.open_target.measurableSet)
      filter_upwards [hae] with x hx
      simp only [Function.comp_apply, hLap _ (e.map_target hx), e.right_inv hx]
    rw [← integral_green_chartTest e C.metric C.smooth_metric μ C.volume_eq G L u y hLap hzero hF,
      hglob.2]
    exact hvu hy

end Kernel

end CalderonN
