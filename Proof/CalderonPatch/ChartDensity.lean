module

public import Proof.CalderonPatch.NativeLaplace

import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.Topology.Compactness.Lindelof
import Proof.CalderonN.LinearMetric

@[expose] public section

noncomputable section
open Filter MeasureTheory Set
open scoped ContDiff ENNReal Manifold Topology

namespace CalderonPatch

open CalderonN (X chartVolume chartVolumeMeasure coordinateJacobian_det_ne_zero
  coordinateMatrix_det_eq chartVolume_pullbackMetric pullbackMetric)

variable {n : ℕ} [NeZero n]

/-- Changing smooth Euclidean charts transports the exact Riemannian
density, with the absolute Jacobian determinant. -/
theorem map_chartVolumeMeasure (e : OpenPartialHomeomorph (X n) (X n))
    (he : ContDiffOn ℝ ∞ e e.source) (γ δ : CalderonN.MetricField n)
    (hγ : EqOn γ (pullbackMetric δ e) e.source) :
    (chartVolumeMeasure e.source γ).map e = chartVolumeMeasure e.target δ := by
  classical
  let w (x : X n) := ENNReal.ofReal (chartVolume δ x)
  let v (x : X n) := ENNReal.ofReal (chartVolume γ x)
  have hSrc := e.open_source.measurableSet
  have hTar := e.open_target.measurableSet
  have hAE : ∀ᵐ x ∂chartVolumeMeasure e.source γ, x ∈ e.source :=
    (withDensity_absolutelyContinuous (volume.restrict e.source) v).ae_le (ae_restrict_mem hSrc)
  have hme : AEMeasurable (e : X n → X n) (chartVolumeMeasure e.source γ) :=
    (e.continuousOn.aemeasurable hSrc).mono_ac (withDensity_absolutelyContinuous _ _)
  ext S hS
  let A := e.source ∩ e ⁻¹' S
  have hAs : A ⊆ e.source := inter_subset_left
  have hA : MeasurableSet A := by
    let f := piecewise e.source (e : X n → X n) (fun _ => 0)
    have hf : Measurable f := e.continuousOn.measurable_piecewise continuous_const.continuousOn hSrc
    have hEq : A = e.source ∩ f ⁻¹' S := by
      ext x
      constructor
      · intro hx
        refine ⟨hx.1, ?_⟩
        change f x ∈ S
        have heS : e x ∈ S := hx.2
        simpa only [f, piecewise_eq_of_mem _ _ _ hx.1] using heS
      · intro hx
        refine ⟨hx.1, ?_⟩
        change e x ∈ S
        have hf : f x ∈ S := hx.2
        simpa only [f, piecewise_eq_of_mem _ _ _ hx.1] using hf
    rw [hEq]
    exact hSrc.inter (hf hS)
  have hImg : e '' A = S ∩ e.target := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨hx.2, e.map_source hx.1⟩
    · rintro ⟨hyS, hy⟩
      refine ⟨e.symm y, ⟨e.map_target hy, ?_⟩, e.right_inv hy⟩
      change e (e.symm y) ∈ S
      rwa [e.right_inv hy]
  have hder (x : X n) (hx : x ∈ A) :
      HasFDerivWithinAt e (fderiv ℝ e x) A x :=
    ((he.contDiffAt (e.open_source.mem_nhds hx.1)).differentiableAt (by simp)).hasFDerivAt.hasFDerivWithinAt
  have hw (x : X n) (hx : x ∈ e.source) :
      v x = ENNReal.ofReal |(fderiv ℝ e x).det| * w (e x) := by
    change ENNReal.ofReal (Real.sqrt (γ x).det) = _
    rw [hγ hx]
    change ENNReal.ofReal (chartVolume (pullbackMetric δ e) x) = _
    rw [chartVolume_pullbackMetric, ENNReal.ofReal_mul (abs_nonneg _)]
    exact congrArg (fun a : ℝ => ENNReal.ofReal |a| * w (e x)) (coordinateMatrix_det_eq _)
  calc
    _ = chartVolumeMeasure e.source γ A := by
      rw [Measure.map_apply_of_aemeasurable hme hS]
      exact (Measure.measure_inter_eq_of_ae hAE).symm
    _ = ∫⁻ x in A, v x ∂volume := by
      change (volume.restrict e.source).withDensity v A = _
      rw [withDensity_apply _ hA, Measure.restrict_restrict_of_subset hAs]
    _ = ∫⁻ x in A, ENNReal.ofReal |(fderiv ℝ e x).det| * w (e x) ∂volume :=
      lintegral_congr_ae (by filter_upwards [ae_restrict_mem hA] with x hx; exact hw x (hAs hx))
    _ = ∫⁻ x in S ∩ e.target, w x ∂volume := by
      rw [← lintegral_image_eq_lintegral_abs_det_fderiv_mul volume hA hder (e.injOn.mono hAs), hImg]
    _ = chartVolumeMeasure e.target δ S := by
      rw [chartVolumeMeasure, withDensity_apply _ hS, Measure.restrict_restrict hS]
      rfl

section Manifold

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace n) M]
  [IsManifold (𝓡∂ n) ∞ M] [MeasurableSpace M] [BorelSpace M]

local notation "J" => 𝓡∂ n
local notation "K" => 𝓘(ℝ, X n)

/-- The frozen volume law transports to an open subset of an extended chart. -/
theorem volume_eq_restricted_extChartAt (g : SmoothMetric n M) (μ : Measure M)
    (hμ : IsMetricVolume g μ) (p : M) {a : OpenPartialHomeomorph M (X n)}
    {V : Set (X n)} (hV : IsOpen V) (hVsub : V ⊆ interior (extChartAt J p).target)
    (hat : a.target = V)
    (has : a.source = (extChartAt J p).source ∩ (extChartAt J p) ⁻¹' V)
    (ha : (a : M → X n) = extChartAt J p)
    (hai : (a.symm : X n → M) = (extChartAt J p).symm) :
    (μ.restrict a.source).map a = chartVolumeMeasure a.target (coordinateMetric g a) := by
  let c := extChartAt J p
  have hc := (isOpen_extChartAt_source (I := J) p).measurableSet
  have hmc := (continuousOn_extChartAt (I := J) p).aemeasurable hc (μ := μ)
  have hmap : (((μ.restrict c.source).map c).restrict V) = (μ.restrict a.source).map a := by
    rw [Measure.restrict_map_of_aemeasurable hmc hV.measurableSet,
      Measure.restrict_restrict' hc, has, inter_comm c.source, ha]
  have hdens : EqOn (chartMetric g p) (coordinateMetric g a) V := by
    intro x hx
    have hxR : x ∈ interior (range J) :=
      interior_mono (extChartAt_target_subset_range (I := J) p) (hVsub hx)
    have hn : range J ∈ 𝓝 x := mem_of_superset (isOpen_interior.mem_nhds hxR) interior_subset
    ext i j
    let f : X n → M := c.symm
    have hD : (mfderivWithin K J f (range J) x : X n →L[ℝ] X n) = mfderiv K J f x :=
      mfderivWithin_of_mem_nhds hn
    change g.inner (f x) (mfderivWithin K J f (range J) x (CalderonN.axis i))
      (mfderivWithin K J f (range J) x (CalderonN.axis j)) = coordinateMetric g a x i j
    calc
      _ = g.inner (f x) (mfderiv K J f x (CalderonN.axis i)) (mfderiv K J f x (CalderonN.axis j)) :=
        congrArg (fun D : X n →L[ℝ] X n => g.inner (f x) (D (CalderonN.axis i)) (D (CalderonN.axis j))) hD
      _ = _ := congrArg (fun q : X n → M =>
        let D := mfderiv K J q x
        g.inner (q x) (D (CalderonN.axis i)) (D (CalderonN.axis j))) hai.symm
  rw [← hmap, hμ p, restrict_withDensity hV.measurableSet,
    Measure.restrict_restrict_of_subset (hVsub.trans interior_subset), hat, chartVolumeMeasure]
  apply withDensity_congr_ae
  filter_upwards [ae_restrict_mem hV.measurableSet] with x hx
  rw [hdens hx]

private theorem volume_agrees_on_transition (g : SmoothMetric n M) (μ : Measure M)
    (a e : OpenPartialHomeomorph M (X n)) (hae : a.source ⊆ e.source)
    (ha : ContMDiffOn J K ∞ a a.source) (has : ContMDiffOn K J ∞ a.symm a.target)
    (he : ContMDiffOn J K ∞ e e.source) (hes : ContMDiffOn K J ∞ e.symm e.target)
    (hVa : (μ.restrict a.source).map a = chartVolumeMeasure a.target (coordinateMetric g a)) :
    let T := a.symm.trans e
    ((μ.restrict e.source).map e).restrict T.target =
      (chartVolumeMeasure e.target (coordinateMetric g e)).restrict T.target := by
  let T := a.symm.trans e
  have hTs : T.source = a.target := inter_eq_left.mpr (fun x hx => hae (a.map_target hx))
  have hTt : T.target ⊆ e.target := fun _ hx => hx.1
  have hpre : e ⁻¹' T.target ∩ e.source = a.source := by
    ext x
    constructor
    · intro hx
      have h := (show e x ∈ e.target ∩ e.symm ⁻¹' a.source from hx.1).2
      change e.symm (e x) ∈ a.source at h
      rwa [e.left_inv hx.2] at h
    · intro hx
      have hxe := hae hx
      refine ⟨⟨e.map_source hxe, ?_⟩, hxe⟩
      change e.symm (e x) ∈ a.source
      rwa [e.left_inv hxe]
  have hmea := e.continuousOn.aemeasurable e.open_source.measurableSet (μ := μ)
  have hmaa := a.continuousOn.aemeasurable a.open_source.measurableSet (μ := μ)
  have hmaT : AEMeasurable (T : X n → X n) ((μ.restrict a.source).map a) := by
    rw [hVa, ← hTs]
    exact (T.continuousOn.aemeasurable T.open_source.measurableSet).mono_ac
      (withDensity_absolutelyContinuous _ _)
  have hcomp : (μ.restrict a.source).map e = ((μ.restrict a.source).map a).map T := by
    rw [AEMeasurable.map_map_of_aemeasurable hmaT hmaa]
    apply Measure.map_congr
    filter_upwards [ae_restrict_mem a.open_source.measurableSet (μ := μ)] with x hx
    change e x = e (a.symm (a x))
    rw [a.left_inv hx]
  have hTD : ContDiffOn ℝ ∞ T T.source :=
    (he.comp (has.mono (fun _ hx => hx.1)) (fun _ hx => hx.2)).contDiffOn
  have hγ : EqOn (coordinateMetric g a) (pullbackMetric (coordinateMetric g e) T) T.source :=
    coordinateMetric_change g e a ⟨he.mdifferentiableOn (by simp), hes.mdifferentiableOn (by simp)⟩
      ⟨ha.mdifferentiableOn (by simp), has.mdifferentiableOn (by simp)⟩
  change ((μ.restrict e.source).map e).restrict T.target = _
  rw [Measure.restrict_map_of_aemeasurable hmea T.open_target.measurableSet,
    Measure.restrict_restrict' e.open_source.measurableSet, hpre, hcomp, hVa, ← hTs,
    map_chartVolumeMeasure T hTD _ _ hγ]
  change chartVolumeMeasure T.target _ = (chartVolumeMeasure e.target _).restrict T.target
  simp only [chartVolumeMeasure, restrict_withDensity T.open_target.measurableSet,
    Measure.restrict_restrict_of_subset hTt]

/-- The canonical volume law fixes the actual density on every smooth
interior coordinate chart. The local change-of-variables identities
agree on a countable cover of the Euclidean target. -/
theorem volume_eq_coordinate (g : SmoothMetric n M) (μ : Measure M) (hμ : IsMetricVolume g μ)
    (e : OpenPartialHomeomorph M (X n)) (hI : e.source ⊆ (𝓡∂ n).interior M)
    (he : ContMDiffOn J K ∞ e e.source) (hes : ContMDiffOn K J ∞ e.symm e.target) :
    (μ.restrict e.source).map e = chartVolumeMeasure e.target (coordinateMetric g e) := by
  let μe := (μ.restrict e.source).map e
  let ν := chartVolumeMeasure e.target (coordinateMetric g e)
  have hloc (z : e.target) :
      ∃ V : Set (X n), (z : X n) ∈ V ∧ V ⊆ e.target ∧ IsOpen V ∧ μe.restrict V = ν.restrict V := by
    let p := e.symm z
    have hp : p ∈ e.source := e.map_target z.property
    let c := extChartAt J p
    let V := interior c.target ∩ c.symm ⁻¹' e.source
    have hV : IsOpen V := ((continuousOn_extChartAt_symm p).mono interior_subset).isOpen_inter_preimage
      isOpen_interior e.open_source
    have hVsub : V ⊆ interior c.target := inter_subset_left
    obtain ⟨a, hat, has, ha, hai, _, hsa, hsai⟩ :=
      exists_interiorChart_restrict p hV (hVsub.trans interior_subset)
    have hpc : p ∈ c.source := mem_extChartAt_source p
    have hpa : p ∈ a.source := by
      rw [has]
      refine ⟨hpc, (𝓡∂ n).isInteriorPoint_iff.mp (hI hp), ?_⟩
      change c.symm (c p) ∈ e.source
      rwa [c.left_inv hpc]
    have hae : a.source ⊆ e.source := by
      intro q hq
      rw [has] at hq
      have h := hq.2.2
      change c.symm (c q) ∈ e.source at h
      rwa [c.left_inv hq.1] at h
    have hVa := volume_eq_restricted_extChartAt g μ hμ p hV hVsub hat has ha hai
    let T := a.symm.trans e
    exact ⟨T.target, ⟨z.property, hpa⟩, fun _ hz => hz.1, T.open_target,
      volume_agrees_on_transition g μ a e hae hsa hsai he hes hVa⟩
  choose V hzV hVe hVo hVeq using hloc
  have hcover : e.target ⊆ ⋃ z, V z := fun x hx => mem_iUnion.mpr ⟨⟨x, hx⟩, hzV ⟨x, hx⟩⟩
  obtain ⟨s, hs, hse⟩ :=
    (HereditarilyLindelofSpace.isLindelof e.target).elim_countable_subcover V hVo hcover
  have hUnion : (⋃ z ∈ s, V z) = e.target :=
    Subset.antisymm (iUnion₂_subset fun z _ => hVe z) hse
  have hEq := (Measure.restrict_biUnion_congr hs).mpr (fun z _ => hVeq z)
  rw [hUnion] at hEq
  have hμe : μe.restrict e.target = μe := by
    have hm := e.continuousOn.aemeasurable e.open_source.measurableSet (μ := μ)
    have hPre : e ⁻¹' e.target ∩ e.source = e.source :=
      inter_eq_right.mpr (fun _ hx => e.map_source hx)
    change ((μ.restrict e.source).map e).restrict e.target = _
    rw [Measure.restrict_map_of_aemeasurable hm e.open_target.measurableSet,
      Measure.restrict_restrict' e.open_source.measurableSet, hPre]
  have hν : ν.restrict e.target = ν := by
    unfold ν chartVolumeMeasure
    rw [restrict_withDensity e.open_target.measurableSet, Measure.restrict_restrict_of_subset Subset.rfl]
  exact hμe.symm.trans (hEq.trans hν)

/-- A smooth interior chart supplies the exact data consumed by the
checked Dirichlet Green restriction. -/
def nativeInteriorMetricChart (g : SmoothMetric n M) (μ : Measure M) (hμ : IsMetricVolume g μ)
    (e : OpenPartialHomeomorph M (X n)) (hI : e.source ⊆ (𝓡∂ n).interior M)
    (he : ContMDiffOn J K ∞ e e.source) (hes : ContMDiffOn K J ∞ e.symm e.target) :
    CalderonN.InteriorMetricChart J μ (nativeLaplace g) where
  chart := e
  source_interior := hI
  smooth := he
  smooth_inverse := hes
  metric := coordinateMetric g e
  smooth_metric := coordinateMetric_smooth g e he hes
  volume_eq := volume_eq_coordinate g μ hμ e hI he hes
  laplace_eq _ hu _ hp := nativeLaplace_eq_coordinate g e hI he hes hu.contMDiffOn hp

theorem restrict_interiorMetricChart {μ : Measure M} {L : (M → ℝ) → M → ℝ}
    (A : CalderonN.InteriorMetricChart J μ L) {U : Set (X n)} (hU : IsOpen U) (hUA : U ⊆ A.chart.target) :
    ∃ B : CalderonN.InteriorMetricChart J μ L,
      B.chart.source = A.chart.source ∩ A.chart ⁻¹' U ∧ B.chart.target = U ∧
      (B.chart.symm : X n → M) = A.chart.symm ∧ B.metric = A.metric := by
  let a := A.chart
  let b := a.trans (OpenPartialHomeomorph.ofSet U hU)
  have hBt : b.target = U := by
    change U ∩ id ⁻¹' a.target = U
    rw [preimage_id]
    exact inter_eq_left.mpr hUA
  have hBs : b.source = a.source ∩ a ⁻¹' U := rfl
  have hBsub : b.source ⊆ a.source := fun x hx => (hBs ▸ hx : x ∈ a.source ∩ _).1
  have hCt : b.target ⊆ a.target := hBt.symm ▸ hUA
  have hVol : (μ.restrict b.source).map b = chartVolumeMeasure b.target A.metric := by
    have ha : AEMeasurable (a : M → X n) (μ.restrict a.source) :=
      a.continuousOn.aemeasurable a.open_source.measurableSet
    change (μ.restrict b.source).map a = _
    have hEq := Measure.restrict_map_of_aemeasurable ha hU.measurableSet
    rw [Measure.restrict_restrict' a.open_source.measurableSet, inter_comm, ← hBs, A.volume_eq] at hEq
    rw [← hEq, hBt]
    simp only [chartVolumeMeasure, restrict_withDensity hU.measurableSet, Measure.restrict_restrict_of_subset hUA]
  exact ⟨⟨b,hBsub.trans A.source_interior,A.smooth.mono hBsub,A.smooth_inverse.mono hCt,
    A.metric,⟨fun i j => (A.smooth_metric.1 i j).mono hCt,fun x hx => A.smooth_metric.2 x (hCt hx)⟩,
    hVol,fun u hu p hp => A.laplace_eq u hu p (hBsub hp)⟩,hBs,hBt,rfl,rfl⟩

end Manifold

end CalderonPatch
