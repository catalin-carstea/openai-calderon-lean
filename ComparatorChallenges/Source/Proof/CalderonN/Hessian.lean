module

public import Proof.CalderonN.Chart
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Proof.CalderonN.DilationHarmonic
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Matrix.Order
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.LinearAlgebra.Matrix.Bilinear
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
public import Proof.CalderonN.Coordinates

public section

open Set Filter
open scoped ContDiff Topology BigOperators

namespace CalderonN

variable {dim : ℕ} [NeZero dim]

theorem hessian_transpose {Ω : Set (X dim)} (hΩ : IsOpen Ω) {u : (X dim) → ℝ}
    (hu : ContDiffOn ℝ ∞ u Ω) {x : (X dim)} (hx : x ∈ Ω) :
    (hessian u x).transpose = hessian u x := sorry

end CalderonN
