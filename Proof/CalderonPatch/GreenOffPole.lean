module

public import Proof.CalderonPatch.ChartDensity

import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
import Mathlib.MeasureTheory.Measure.OpenPos
import Proof.CalderonN.ChartGeometry
import Proof.CalderonN.GreenWeak
import Proof.CalderonN.MetricCalculus

@[expose] public section

noncomputable section
open Filter MeasureTheory Set
open scoped ContDiff Manifold

namespace CalderonPatch

open CalderonN (X I laplace chartVolume chartVolumeMeasure coordDeriv InteriorMetricChart
  Harmonic IsDirichletGreenKernel tsupport_laplace_subset laplace_congrOn integral_green_chartTest
  chartTest tsupport_chartTest_subset hasCompactSupport_chartTest contMDiff_chartTest
  integral_laplace_symmetric_of_compact_test)

variable {n : ℕ}

/-- The homogeneous version of the weak-to-classical argument in
`GreenGerm.harmonic_left` from the adopted check `0d2e9641`. -/
theorem harmonic_of_zero_laplace_tests {U : Set (X n)} (hU : IsOpen U)
    {g : CalderonN.MetricField n} (hg : CalderonN.SmoothMetric U g)
    {u : X n → ℝ} (hu : ContDiffOn ℝ ∞ u U)
    (hTest : ∀ φ : X n → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ U →
      (∫ x in U, u x * (-laplace g φ x) * chartVolume g x) = 0) :
    Harmonic U g u := by
  let D (x : X n) := chartVolume g x * laplace g u x
  have hD : ContinuousOn D U :=
    ((CalderonN.contDiffOn_metric_volume hg).mul (contDiffOn_coordinateLaplace hU hg hu)).continuousOn
  have htests (φ : X n → ℝ) (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ)
      (hφU : tsupport φ ⊆ U) : (∫ x, φ x • D x) = 0 := by
    have hzero := hTest φ hφ hφc hφU
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx => by
      have hz : laplace g φ x = 0 := image_eq_zero_of_notMem_tsupport (fun h =>
        hx (hφU (tsupport_laplace_subset g φ h)))
      simp [hz])] at hzero
    have hzero' : (∫ x, u x * laplace g φ x * chartVolume g x) = 0 := by
      simpa only [mul_neg, neg_mul, integral_neg, neg_eq_zero] using hzero
    exact (integral_laplace_symmetric_of_compact_test hU hg hu hφ hφc hφU).symm.trans hzero'
  have hAE : D =ᵐ[(volume : Measure (X n)).restrict U] 0 :=
    (ae_restrict_iff' hU.measurableSet).mpr
      (hU.ae_eq_zero_of_integral_contDiff_smul_eq_zero (hD.locallyIntegrableOn hU.measurableSet) htests)
  have he : EqOn D 0 U := Measure.eqOn_open_of_ae_eq hAE hU hD continuousOn_const
  exact ⟨hu, fun x hx => (mul_eq_zero.mp (he hx)).resolve_left
    (Real.sqrt_pos.mpr (hg.2 x hx).det_pos).ne'⟩

variable [NeZero n] {M : Type*} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanHalfSpace n) M] [IsManifold (𝓡∂ n) ∞ M]
  [MeasurableSpace M] [BorelSpace M]

local notation "J" => 𝓡∂ n
local notation "K" => 𝓘(ℝ, X n)
local notation "R" => 𝓘(ℝ, ℝ)

/-- A genuine Dirichlet Green section satisfies the homogeneous equation
throughout any interior chart that excludes its ambient pole. -/
theorem harmonic_greenSection_off_pole {μ : Measure M} {L : (M → ℝ) → M → ℝ}
    (C : InteriorMetricChart J μ L)
    (hloc : ∀ v : M → ℝ, ContMDiff J R ∞ v → tsupport (L v) ⊆ tsupport v)
    {G : M × M → ℝ} (hG : IsDirichletGreenKernel J μ L G)
    {q : M} (hq : q ∈ (𝓡∂ n).interior M) (hqout : q ∉ C.chart.source) :
    Harmonic C.chart.target C.metric (fun x => G (C.chart.symm x, q)) := by
  let e := C.chart
  let f : X n → ℝ := fun x => G (e.symm x, q)
  have hf : ContDiffOn ℝ ∞ f e.target := by
    apply ContMDiffOn.contDiffOn
    apply hG.smooth_off_diagonal.comp (C.smooth_inverse.prodMk contMDiffOn_const)
    intro x hx
    refine ⟨C.source_interior (e.map_target hx), hq, ?_⟩
    change e.symm x ≠ q
    intro h
    exact hqout (h ▸ e.map_target hx)
  apply harmonic_of_zero_laplace_tests e.open_target C.smooth_metric hf
  intro u hu huc hus
  let v := chartTest e u
  have hv : ContMDiff J R ∞ v := contMDiff_chartTest e C.smooth hu huc hus
  have hvs : tsupport v ⊆ e.source := (tsupport_chartTest_subset e huc hus).trans
    (fun _ ⟨x, hx, he⟩ => he ▸ e.map_target (hus hx))
  have hvq : v q = 0 := image_eq_zero_of_notMem_tsupport (fun h => hqout (hvs h))
  have hglob := (hG.weak_inverse q hq v hv (hasCompactSupport_chartTest e huc hus)
    (hvs.trans C.source_interior)).2
  have hvu : EqOn (v ∘ e.symm) u e.target := by
    intro x hx
    simp only [v, chartTest, Function.comp_apply, indicator_of_mem (e.map_target hx), e.right_inv hx]
  have hLap : ∀ p ∈ e.source, L v p = laplace C.metric u (e p) := by
    intro p hp
    exact (C.laplace_eq v hv p hp).trans
      (laplace_congrOn e.open_target (fun _ _ => rfl) hvu (e.map_source hp))
  have hzero : ∀ p ∉ e.source, L v p = 0 := fun p hp =>
    image_eq_zero_of_notMem_tsupport (fun h => hp (hvs (hloc v hv h)))
  have hF : AEStronglyMeasurable (fun x => f x * (-laplace C.metric u x))
      (chartVolumeMeasure e.target C.metric) := by
    have hc := (hf.mul (contDiffOn_coordinateLaplace e.open_target C.smooth_metric hu.contDiffOn).neg).continuousOn
    exact AEStronglyMeasurable.mono_ac (withDensity_absolutelyContinuous _ _)
      (hc.aemeasurable e.open_target.measurableSet).aestronglyMeasurable
  let G' : M × M → ℝ := fun p => G (p.1, q)
  have hpush := integral_green_chartTest e C.metric C.smooth_metric μ C.volume_eq G' L u 0 hLap hzero hF
  exact hpush.symm.trans (hglob.trans hvq)

end CalderonPatch
