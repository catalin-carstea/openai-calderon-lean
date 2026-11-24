module

public import Proof.CalderonN.MetricConnection
public import Proof.CalderonN.MetricVolumeDifferential
public import Proof.CalderonN.Chart
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic
public import Proof.CalderonN.Coordinates

@[expose] public section

/- Port of MetricDensity.lean from the checked Proposition 5.3 release f308cb9d. -/
noncomputable section
open Set Filter MeasureTheory MvPolynomial
open scoped ContDiff Topology
namespace CalderonN
variable {n : ℕ}

abbrev metricDensity (g : (MetricField n)) (x : (X n)) : ℝ := chartVolume g x

end CalderonN
