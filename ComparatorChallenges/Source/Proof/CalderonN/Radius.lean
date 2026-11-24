module

public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Topology.MetricSpace.Pseudo.Lemmas
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

@[expose] public section

noncomputable section
open Set Filter
open scoped Topology

namespace CalderonN

/-- The scalar profile ℓδ in the shrinking radii of Section 4.2. -/
def softplus (δ t : ℝ) : ℝ :=
  δ * Real.log (1 + Real.exp (t / δ))

/-- The radius of the normal sphere at each center. -/
def shrinkingRadius {E : Type*} (R : ℝ) (p : ℕ) (depth : E → ℝ) (δ : ℝ) (y : E) : ℝ :=
  R * (softplus δ (depth y)) ^ p

end CalderonN
