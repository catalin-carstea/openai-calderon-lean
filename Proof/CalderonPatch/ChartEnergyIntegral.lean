module

public import Proof.CalderonPatch.ChartDensity
public import Proof.CalderonPatch.CoordinateEnergy
public import Proof.CalderonPatch.DirichletMinimization
public import Proof.CalderonN.MetricDivergence

import Proof.CalderonN.ChartBilinear
import Proof.CalderonN.ChartGeometry
import Proof.CalderonN.GreenWeak
import Proof.CalderonN.MetricCalculus
import Proof.CalderonN.ProductPhaseAlgebra

public section

noncomputable section
open MeasureTheory Set
open scoped ContDiff Manifold

namespace CalderonPatch

open CalderonN (I X InteriorMetricChart chartMetricGradient chartVolume chartVolumeMeasure
  coordDeriv divergenceCoeff divergenceFlux laplace metricPair metricPair_metricGradient)

variable {n : ℕ} [NeZero n] {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace n) M] [IsManifold (𝓡∂ n) ∞ M]

local notation "J" => 𝓡∂ n
local notation "K" => 𝓘(ℝ, X n)
local notation "R" => 𝓘(ℝ, ℝ)

/-- The polarized native gradient energy in an interior chart is the
ordinary derivative of the second function evaluated on the coordinate
metric gradient of the first function. -/
theorem energyPairingDensity_in_coordinates (g : SmoothMetric n M)
    (e : OpenPartialHomeomorph M (X n)) (he : ContMDiffOn J K ∞ e e.source)
    (hes : ContMDiffOn K J ∞ e.symm e.target) {u v : M → ℝ}
    (hu : ContMDiffOn J R ∞ u e.source) (hv : ContMDiffOn J R ∞ v e.source)
    {x : X n} (hx : x ∈ e.target) :
    energyPairingDensity g u v (e.symm x) = ∑ i : I n,
      coordDeriv i (v ∘ e.symm) x * chartMetricGradient (coordinateMetric g e) (u ∘ e.symm) x i := by
  let p := e.symm x
  let D : X n →L[ℝ] X n := mfderiv K J e.symm x
  let γ := coordinateMetric g e
  let A : X n →L[ℝ] ℝ := mfderiv J R u p
  let B : X n →L[ℝ] ℝ := mfderiv J R v p
  let w := chartMetricGradient γ (u ∘ e.symm) x
  let z := chartMetricGradient γ (v ∘ e.symm) x
  have hw : metricDual g p A = D w := metricDual_in_coordinates g e he hes hu hx
  have hz : metricDual g p B = D z := metricDual_in_coordinates g e he hes hv hx
  change g.inner p (metricDual g p A) (metricDual g p B) = _
  calc
    _ = g.inner p (D z) (D w) := (g.symm p _ _).trans
      (congrArg₂ (fun a b : X n => g.inner p a b) hz hw)
    _ = metricPair γ x z w := (realizesCoordinateMetric g e x hx z w).symm
    _ = _ := metricPair_metricGradient γ (v ∘ e.symm) x w
      ((coordinateMetric_smooth g e he hes).2 x hx)

variable [MeasurableSpace M] [BorelSpace M]

omit [IsManifold (𝓡∂ n) ∞ M] in
/-- An integrand with a continuous coordinate representative can be
integrated in the chart using its actual Riemannian density. -/
theorem integral_interiorChart_of_coordinateRepresentation
    {μ : Measure M} {L : (M → ℝ) → M → ℝ} (C : InteriorMetricChart J μ L)
    {w : M → ℝ} {f : X n → ℝ} (hf : ContinuousOn f C.chart.target)
    (hEq : EqOn (w ∘ C.chart.symm) f C.chart.target) :
    (∫ p in C.chart.source, w p ∂μ) =
      ∫ x in C.chart.target, f x * chartVolume C.metric x := by
  let e := C.chart
  have he : AEMeasurable (e : M → X n) (μ.restrict e.source) :=
    e.continuousOn.aemeasurable e.open_source.measurableSet
  have hfM : AEStronglyMeasurable f (chartVolumeMeasure e.target C.metric) :=
    (hf.aestronglyMeasurable e.open_target.measurableSet).mono_ac
      (withDensity_absolutelyContinuous _ _)
  calc
    _ = ∫ p in e.source, f (e p) ∂μ := by
      apply setIntegral_congr_fun e.open_source.measurableSet
      intro p hp
      have hh := hEq (e.map_source hp)
      rwa [Function.comp_apply, e.left_inv hp] at hh
    _ = ∫ x, f x ∂chartVolumeMeasure e.target C.metric := by
      rw [← C.volume_eq, integral_map he]
      exact C.volume_eq ▸ hfM
    _ = _ := CalderonN.integral_chartVolume e.open_target C.metric C.smooth_metric f

omit [NeZero n] in
private theorem chartGradientPairing_mul_volume (γ : CalderonN.MetricField n)
    (u v : X n → ℝ) (x : X n) :
    (∑ i : I n, coordDeriv i v x * chartMetricGradient γ u x i) * chartVolume γ x =
      ∑ i : I n, coordDeriv i v x * divergenceFlux γ u x i := by
  unfold divergenceFlux divergenceCoeff
  simp only [chartMetricGradient, Finset.sum_mul, Finset.mul_sum, mul_assoc]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- The native energy pairing over the chart is the volume-weighted
coordinate gradient pairing used in the divergence formula. -/
theorem integral_energyPairingDensity_in_coordinates (g : SmoothMetric n M)
    (μ : Measure M) (hμ : IsMetricVolume g μ)
    (e : OpenPartialHomeomorph M (X n)) (heI : e.source ⊆ (J).interior M)
    (he : ContMDiffOn J K ∞ e e.source) (hes : ContMDiffOn K J ∞ e.symm e.target)
    {u v : M → ℝ} (hu : ContMDiffOn J R ∞ u e.source) (hv : ContMDiffOn J R ∞ v e.source) :
    (∫ p in e.source, energyPairingDensity g u v p ∂μ) =
      ∫ x in e.target, ∑ i : I n, coordDeriv i (v ∘ e.symm) x *
        divergenceFlux (coordinateMetric g e) (u ∘ e.symm) x i := by
  let γ := coordinateMetric g e
  let a := u ∘ e.symm
  let b := v ∘ e.symm
  let f (x : X n) := ∑ i : I n, coordDeriv i b x * chartMetricGradient γ a x i
  have hγ := coordinateMetric_smooth g e he hes
  have ha : ContDiffOn ℝ ∞ a e.target := (hu.comp hes e.symm.mapsTo).contDiffOn
  have hb : ContDiffOn ℝ ∞ b e.target := (hv.comp hes e.symm.mapsTo).contDiffOn
  have hf : ContinuousOn f e.target := by
    apply ContDiffOn.continuousOn (𝕜 := ℝ) (n := ∞)
    apply ContDiffOn.sum
    intro i _
    apply (CalderonN.contDiffOn_coordDeriv hb e.open_target i).mul
    change ContDiffOn ℝ ∞ (fun x => ∑ j : I n, (γ x)⁻¹ i j * coordDeriv j a x) e.target
    exact ContDiffOn.sum fun j _ => (CalderonN.contDiffOn_metric_inv_entry hγ i j).mul
      (CalderonN.contDiffOn_coordDeriv ha e.open_target j)
  let C := nativeInteriorMetricChart g μ hμ e heI he hes
  have hRel : EqOn (energyPairingDensity g u v ∘ C.chart.symm) f C.chart.target :=
    fun x hx => energyPairingDensity_in_coordinates g e he hes hu hv hx
  calc
    _ = ∫ x in e.target, f x * chartVolume γ x :=
      integral_interiorChart_of_coordinateRepresentation C hf hRel
    _ = _ := by
      apply setIntegral_congr_fun e.open_target.measurableSet
      intro x _
      exact chartGradientPairing_mul_volume γ a b x

/-- The complete Green pairing on the native interior chart agrees
with its coordinate expression for any smooth representatives of the
functions and of the metric. -/
theorem integral_nativeGreenPairing_in_coordinates (g : SmoothMetric n M)
    (μ : Measure M) (hμ : IsMetricVolume g μ)
    (e : OpenPartialHomeomorph M (X n)) (heI : e.source ⊆ (J).interior M)
    (he : ContMDiffOn J K ∞ e e.source) (hes : ContMDiffOn K J ∞ e.symm e.target)
    {u v : M → ℝ} (hu : ContMDiffOn J R ∞ u e.source) (hv : ContMDiffOn J R ∞ v e.source)
    {γ : CalderonN.MetricField n} (hMetric : EqOn (coordinateMetric g e) γ e.target)
    {a b : X n → ℝ} (hA : EqOn (u ∘ e.symm) a e.target) (hB : EqOn (v ∘ e.symm) b e.target) :
    (∫ p in e.source, v p * nativeLaplace g u p + energyPairingDensity g u v p ∂μ) =
      ∫ x in e.target, b x * (chartVolume γ x * laplace γ a x) +
        ∑ i : I n, coordDeriv i b x * divergenceFlux γ a x i := by
  let C := nativeInteriorMetricChart g μ hμ e heI he hes
  let f (x : X n) := b x * laplace γ a x + ∑ i : I n,
    coordDeriv i b x * chartMetricGradient γ a x i
  have hγ : CalderonN.SmoothMetric e.target γ := by
    refine ⟨fun i j => (C.smooth_metric.1 i j).congr ?_, ?_⟩
    · intro x hx
      exact congrArg (fun G : CalderonN.Mat n => G i j) (hMetric hx).symm
    · intro x hx
      rw [← hMetric hx]
      exact C.smooth_metric.2 x hx
  have ha : ContDiffOn ℝ ∞ a e.target := (hu.comp hes e.symm.mapsTo).contDiffOn.congr hA.symm
  have hb : ContDiffOn ℝ ∞ b e.target := (hv.comp hes e.symm.mapsTo).contDiffOn.congr hB.symm
  have hf : ContinuousOn f e.target := by
    apply ContDiffOn.continuousOn (𝕜 := ℝ) (n := ∞)
    apply (hb.mul (contDiffOn_coordinateLaplace e.open_target hγ ha)).add
    apply ContDiffOn.sum
    intro i _
    apply (CalderonN.contDiffOn_coordDeriv hb e.open_target i).mul
    change ContDiffOn ℝ ∞ (fun x => ∑ j : I n, (γ x)⁻¹ i j * coordDeriv j a x) e.target
    exact ContDiffOn.sum fun j _ => (CalderonN.contDiffOn_metric_inv_entry hγ i j).mul
      (CalderonN.contDiffOn_coordDeriv ha e.open_target j)
  have hRel : EqOn ((fun p => v p * nativeLaplace g u p + energyPairingDensity g u v p) ∘
      e.symm) f e.target := by
    intro x hx
    have hLap := nativeLaplace_eq_coordinate g e heI he hes hu (e.map_target hx)
    rw [e.right_inv hx, CalderonN.laplace_congrOn e.open_target hMetric hA hx] at hLap
    have hv0 : v (e.symm x) = b x := hB hx
    have hAu (i : I n) := CalderonN.eqOn_coordDeriv e.open_target hA i hx
    have hBv (i : I n) := CalderonN.eqOn_coordDeriv e.open_target hB i hx
    change v (e.symm x) * nativeLaplace g u (e.symm x) +
      energyPairingDensity g u v (e.symm x) = _
    rw [hLap, hv0, energyPairingDensity_in_coordinates g e he hes hu hv hx]
    simp only [f, chartMetricGradient, hMetric hx, hAu, hBv]
  calc
    _ = ∫ x in e.target, f x * chartVolume (coordinateMetric g e) x :=
      integral_interiorChart_of_coordinateRepresentation C hf hRel
    _ = _ := by
      apply setIntegral_congr_fun e.open_target.measurableSet
      intro x hx
      have hVolume : chartVolume (coordinateMetric g e) x = chartVolume γ x :=
        congrArg (fun G : CalderonN.Mat n => Real.sqrt G.det) (hMetric hx)
      change f x * chartVolume (coordinateMetric g e) x =
        b x * (chartVolume γ x * laplace γ a x) + ∑ i : I n, coordDeriv i b x * divergenceFlux γ a x i
      rw [hVolume]
      unfold f
      rw [add_mul, chartGradientPairing_mul_volume]
      congr 1
      ring

end CalderonPatch
