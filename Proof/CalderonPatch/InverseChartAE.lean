module

public import Proof.CalderonPatch.ChartDensity

public section

noncomputable section
open Filter MeasureTheory Set
open scoped ContDiff Manifold

namespace CalderonPatch

open CalderonN (X)

variable {n : ℕ} [NeZero n] {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace n) M] [IsManifold (𝓡∂ n) ∞ M]
  [MeasurableSpace M] [BorelSpace M]

local notation "J" => 𝓡∂ n
local notation "K" => 𝓘(ℝ, X n)

/-- A coordinate almost-everywhere reading of a property of native
points transfers to the metric volume on the actual chart source. -/
theorem ae_native_of_ae_coordinate (g : SmoothMetric n M) (μ : Measure M) (hμ : IsMetricVolume g μ)
    (e : OpenPartialHomeomorph M (X n)) (heI : e.source ⊆ (J).interior M)
    (he : ContMDiffOn J K ∞ e e.source) (hes : ContMDiffOn K J ∞ e.symm e.target)
    {Q : M → Prop} (hQ : ∀ᵐ z ∂(volume : Measure (X n)).restrict e.target, Q (e.symm z)) :
    ∀ᵐ x ∂μ.restrict e.source, Q x := by
  let ν := CalderonN.chartVolumeMeasure e.target (coordinateMetric g e)
  have heν : (μ.restrict e.source).map e = ν := volume_eq_coordinate g μ hμ e heI he hes
  have hA : ν ≪ (volume : Measure (X n)).restrict e.target :=
    withDensity_absolutelyContinuous _ _
  have heM : AEMeasurable (e : M → X n) (μ.restrict e.source) :=
    e.continuousOn.aemeasurable e.open_source.measurableSet
  have hν : ∀ᵐ z ∂ν, Q (e.symm z) := hQ.filter_mono hA.ae_le
  rw [← heν] at hν
  filter_upwards [ae_of_ae_map heM hν,ae_restrict_mem e.open_source.measurableSet] with x hx hxs
  simpa only [e.left_inv hxs] using hx

end CalderonPatch
