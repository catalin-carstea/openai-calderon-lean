module

public import Proof.CalderonN.MovingBallFamilies
public import Proof.CalderonN.NormalFluxDensity
import Mathlib.Tactic
public import Proof.CalderonN.Coordinates
public import Proof.CalderonN.FixedBallGreenPairing
public import Proof.CalderonN.NormalBallChart
public import Proof.CalderonN.ParametricBallConormal

/-! Adapted from `MovingGreenFluxDensity` in the checked Theorem 3.1 release. -/

public section

set_option maxHeartbeats 2400000
noncomputable section
open Set Metric MeasureTheory
open scoped ContDiff Topology Matrix

namespace CalderonN

variable {dim : ℕ} [NeZero dim] [Nontrivial (Fin dim)]

/-- Evaluate the conormal of boundary data itself, as opposed to the
conormal of its harmonic replacement. -/
@[expose] def rawParametricBallConormal
    (g : (X dim) × (X dim) → (Mat dim)) (b : (X dim) × (X dim) → ℝ) (q : (X dim) × (X dim)) : ℝ :=
  ballConormal (fun z => g (q.1,z)) (fun z => b (q.1,z)) q.2

@[expose] def framedMovingGreenKernel
    (E : (X dim) × (X dim) → (X dim)) (e : (Frame dim)) (r : (X dim) → ℝ) (G : (X dim) × (X dim) → ℝ) (q : (X dim) × (X dim)) : ℝ :=
  G (normalBallChartMap E e q.1 (r q.1) q.2,q.1)

/-- Surface density for the literal Green transfer, extended in the
angular variable along rays in the normal frame. -/
@[expose] def movingGreenFluxDensity
    (γ g : (MetricField dim)) (E : (X dim) × (X dim) → (X dim)) (e : (Frame dim)) (r : (X dim) → ℝ)
    (G : (X dim) × (X dim) → ℝ) (q : (X dim) × (X dim)) : ℝ :=
  let g' := movingBallMetric g E e r
  let b := framedMovingGreenKernel E e r G
  let p := movingBallToFrame γ e q
  (unitSphereArea dim) * ((r q.1)^(dim-2) *
    (parametricBallConormal g' b p - rawParametricBallConormal g' b (p.1,sphereNormalize p.2)))

end CalderonN
