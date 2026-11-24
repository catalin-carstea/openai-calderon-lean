module

public import Proof.CalderonN.FixedBallGreenPairing
public import Proof.CalderonN.SmoothSphereRotation
import Proof.CalderonN.LinearMetric
import Mathlib.Analysis.Calculus.ContDiff.WithLp
import Mathlib.Tactic
public import Proof.CalderonN.Coordinates
public import Proof.CalderonN.MetricDivergence

/-! Adapted from `ConormalDecomposition` in the checked Theorem 3.1 release. -/

public section

set_option maxHeartbeats 1600000

noncomputable section
open Set
open scoped ContDiff InnerProductSpace Matrix

namespace CalderonN

variable {dim : ℕ} [NeZero dim]

open OAI.AnisotropicCalderon.SmoothSphereRotation

/-- The directional vector of the metric conormal in the fixed ball. -/
@[expose] def ballConormalVector (g : (MetricField dim)) (w : (X dim)) : (X dim) :=
  WithLp.toLp 2 (fun j => ∑ i, w i * divergenceCoeff g w i j)

/-- Decompose velocity into the metric conormal and a Euclidean tangential vector. -/
@[expose] def conormalComponent (g : (MetricField dim)) (w V : (X dim)) : ℝ :=
  ⟪w,V⟫_ℝ / ⟪w,ballConormalVector g w⟫_ℝ

@[expose] def tangentialComponent (g : (MetricField dim)) (w V : (X dim)) : (X dim) :=
  V - conormalComponent g w V • ballConormalVector g w

end CalderonN
