module

public import Proof.CalderonN.DilationHarmonic
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
public import Proof.CalderonN.Coordinates

@[expose] public section

noncomputable section
open Set MeasureTheory Filter
open scoped ContDiff ENNReal Pointwise

/- Port of the chart Green dilation law from the 3D Theorem 3.1 release (55d37bfe). -/

namespace CalderonN

variable {n : ℕ}

/-- Under spatial dilation a volume-normalized Green kernel acquires the factor λ^(n−2). -/
def dilatedGreen (G : X n × X n → ℝ) (lam : ℝ) (p : X n × X n) : ℝ :=
  lam ^ (n - 2) * G (lam • p.1, lam • p.2)

end CalderonN
