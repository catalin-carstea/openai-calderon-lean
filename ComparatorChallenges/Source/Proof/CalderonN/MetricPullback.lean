module

public import Proof.CalderonN.Piola
public import Proof.CalderonN.MetricDivergence
import Proof.CalderonN.Chart
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Calculus.ContDiff.WithLp
import Mathlib.Tactic
public import Proof.CalderonN.Coordinates

@[expose] public section

noncomputable section
open Set Filter
open scoped ContDiff Matrix Topology

namespace CalderonN

variable {dim : ℕ} [NeZero dim]

/-- Covariant metric in a general smooth coordinate map. -/
@[expose] def pullbackMetric (g : (MetricField dim)) (F : (X dim) → (X dim)) (x : (X dim)) : (Mat dim) :=
  (coordinateJacobian F x)ᵀ * g (F x) * coordinateJacobian F x

@[expose] def metricFluxVector (g : (MetricField dim)) (u : (X dim) → ℝ) (x : (X dim)) : (X dim) :=
  WithLp.toLp 2 (fun i => divergenceFlux g u x i)

end CalderonN
