module

public import Proof.CalderonPatch.MetricDualEnergy
import Mathlib.Geometry.Manifold.Algebra.LieGroup
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
import Mathlib.Geometry.Manifold.MFDeriv.SpecificFunctions
public import Proof.CalderonN.Coordinates
public import Proof.CalderonPatch.Energy

@[expose] public section

noncomputable section
open Filter MeasureTheory Set
open scoped ContDiff Manifold Topology

namespace CalderonPatch

variable {n : ℕ} [NeZero n] {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace n) M] [IsManifold (𝓡∂ n) 1 M]

local notation "J" => 𝓡∂ n
local notation "R" => 𝓘(ℝ, ℝ)

/-- The pointwise polarized gradient energy in the actual tangent metric. -/
def energyPairingDensity (g : SmoothMetric n M) (u v : M → ℝ) (x : M) : ℝ :=
  g.inner x (metricDual g x (mfderiv J R u x)) (metricDual g x (mfderiv J R v x))

theorem energyPairingDensity_symm (g : SmoothMetric n M) (u v : M → ℝ) (x : M) :
    energyPairingDensity g u v x = energyPairingDensity g v u x := sorry

theorem energyPairingDensity_add_left (g : SmoothMetric n M) {u v : M → ℝ}
    (hu : ContMDiff J R ∞ u) (hv : ContMDiff J R ∞ v) (w : M → ℝ) (x : M) :
    energyPairingDensity g (u + v) w x =
      energyPairingDensity g u w x + energyPairingDensity g v w x := sorry

variable [MeasurableSpace M]

end CalderonPatch
