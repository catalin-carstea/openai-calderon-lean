module

public import Proof.CalderonN.Chart
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Topology.Order.Compact
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
public import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.LinearAlgebra.Matrix.BilinearForm
import Mathlib.Tactic
public import Proof.CalderonN.Coordinates

public section

noncomputable section

open Set Matrix
open scoped ContDiff Matrix.Norms.Elementwise

namespace CalderonN

variable {n : ℕ} [NeZero n]

private abbrev pair (M : Mat n) (v w : X n) : ℝ :=
  metricPair (fun _ => M) 0 v w

private def metricOrthogonalize (M : Mat n) (u : I n → X n) (p i : I n) : X n :=
  if i = p then (Real.sqrt (pair M (u p) (u p)))⁻¹ • u p
  else if p < i then u i - (pair M (u p) (u i) / pair M (u p) (u p)) • u p
  else u i

private def gramSchmidtColumn (M : Mat n) : ℕ → I n → X n
  | 0 => axis
  | k+1 =>
    if hk : k < n then metricOrthogonalize M (gramSchmidtColumn M k) ⟨k,hk⟩
    else gramSchmidtColumn M k

/-- The coordinate Gram–Schmidt frame for an arbitrary positive definite
matrix, in the given order of its coordinate axes. -/
def smoothMetricFrame (M : Mat n) : I n → X n :=
  gramSchmidtColumn M n

end CalderonN
