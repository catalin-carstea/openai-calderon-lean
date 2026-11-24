module

public import Proof.CalderonN.SphereFrame
public import Proof.CalderonN.Chart
public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Analysis.Matrix.Normed
public import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Tactic
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
public import Mathlib.Analysis.Calculus.FDeriv.Symmetric
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
public import Proof.CalderonN.FramePullback
public import Proof.CalderonN.MetricConnection
public import Mathlib.Analysis.CStarAlgebra.Matrix
public import Mathlib.Algebra.Star.StarAlgHom
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Topology.Order.Compact
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
public import Proof.CalderonN.Coordinates

@[expose] public section

noncomputable section
open scoped InnerProductSpace
open Matrix

namespace CalderonN

variable {dim : ℕ} [NeZero dim]

/-- The linear map sending frame coordinates to chart coordinates. -/
@[expose] def frameVectorL (e : (I dim) → (X dim)) : (X dim) →L[ℝ] (X dim) :=
  frameVectorLinear (fun _ => e) 0

end CalderonN
