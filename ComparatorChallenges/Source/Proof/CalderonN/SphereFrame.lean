module

public import Proof.CalderonN.Coercivity
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.Tactic.Ring
public import Proof.CalderonN.Coordinates

/-! The frame identities in the released Proposition 5.3's
`Proof/MetricAlgebra.lean`, over the module-enabled definitions. -/

public section

noncomputable section
open Set
open scoped InnerProductSpace
namespace CalderonN

variable {n : ℕ}

/-- Reconstruction of a tangent vector from coordinates in the chosen orthonormal frame. -/
@[expose] def frameVector (e : Frame n) (y : X n) (w : X n) : X n := ∑ i, w i • e y i

/-- Coordinates of a tangent vector in a metric-orthonormal frame. -/
@[expose] def frameCoordinates (g : MetricField n) (y : X n) (e : I n → X n) (x : X n) : X n :=
  WithLp.toLp 2 fun i => metricPair g y x (e i)

end CalderonN
