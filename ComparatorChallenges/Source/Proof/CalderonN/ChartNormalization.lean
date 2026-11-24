module

public import Proof.CalderonN.Chart
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Proof.CalderonN.LinearMetric
import Proof.CalderonN.MetricDivergence
import Mathlib.Tactic
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.InnerProductSpace.PiL2
public import Proof.CalderonN.Coordinates

public section

noncomputable section
open Set Metric
open scoped ContDiff

namespace CalderonN

variable {n : ℕ} [NeZero n]

/-- A smooth known side whose defining differential is the selected normal coordinate
projection. This is the geometric input to the fixed dilated lower strips. -/
@[expose] def ContainsAlignedSide (normal : (I n)) (Ω W : Set (X n)) : Prop :=
  ∃ (V : Set (X n)) (s : (X n) → ℝ), IsOpen V ∧ (0 : (X n)) ∈ V ∧ V ⊆ Ω ∧
    ContDiffOn ℝ ∞ s V ∧ s 0 = 0 ∧ (∀ v : (X n), fderiv ℝ s 0 v = v normal) ∧
    {x ∈ V | s x < 0} ⊆ W

end CalderonN
