module

public import Proof.CalderonN.Coercivity
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
public import Mathlib.Analysis.Normed.Module.Ball.Pointwise
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Tactic
public import Proof.CalderonN.Coordinates

/-! The polar integration argument is adapted from
`Proof/Archive/ActualRadialDivergencePolarIntegration.lean`,
`ActualRadialDivergenceFubini.lean` and `ActualBallDivergenceFlux.lean`
in Proposition 5.3 release
`f308cb9d8751b6590c8caa28736de77e063a41e1af8cad4e9dfa94819a8299b8`. -/

@[expose] public section

noncomputable section
open MeasureTheory Metric Set
open scoped InnerProductSpace

namespace CalderonN

variable {dim : ℕ} [NeZero dim]

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

abbrev chartSurfaceMeasure (dim : ℕ) : Measure ↥(sphere (0 : (X dim)) 1) := (volume : Measure (X dim)).toSphere

/-- The outward flux of a chart vector density on the unit sphere. -/
@[expose] def unitSphereFlux (W : (X dim) → (X dim)) : ℝ :=
  ∫ w : ↥(sphere (0 : (X dim)) 1), ⟪(w : (X dim)),W w⟫_ℝ ∂(chartSurfaceMeasure dim)



end CalderonN
