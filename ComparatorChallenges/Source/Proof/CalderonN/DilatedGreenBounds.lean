module

public import Proof.CalderonN.GreenDilation
public import Proof.CalderonN.GreenCross
import Mathlib.Tactic
public import Proof.CalderonN.Coordinates

public section

/-! The normalization and fixed-window bounds of the original
`DilatedGreenBounds`, with the distance power for ambient dimension `n`. -/
noncomputable section
open Set Filter Metric
open scoped Topology ContDiff

namespace CalderonN
variable {n : ℕ}

/-- The two prescribed Green pieces before continuation. -/
def dilatedInitialGreen (W : Set (X n)) (G₁ G₂ : X n × X n → ℝ) (lam : ℝ) : X n × X n → ℝ :=
  initialGreenKernel {x | lam • x ∈ W} (dilatedGreen G₁ lam) (dilatedGreen G₂ lam)

end CalderonN
