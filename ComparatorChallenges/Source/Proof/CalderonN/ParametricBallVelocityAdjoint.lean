module

public import Proof.CalderonN.ParametricBallConormal
public import Proof.CalderonN.ConormalDecomposition
public import Proof.CalderonN.NormalFluxDensity
import Proof.CalderonN.Chart
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.Tactic
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
public import Proof.CalderonN.Coordinates
public import Proof.CalderonN.SmoothSphereRotation

/-! Adapted from `ParametricBallVelocityAdjoint` in the checked Theorem 3.1 release. -/

public section

set_option maxHeartbeats 1600000

noncomputable section
open Set Filter Metric MeasureTheory
open scoped ContDiff Topology InnerProductSpace

namespace CalderonN

variable {dim : ℕ} [NeZero dim] [Nontrivial (Fin dim)]
open OAI.AnisotropicCalderon.SmoothSphereRotation

variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]

@[expose] def velocityBoundaryDatum
    (g : P × (X dim) → (Mat dim)) (V : P × (X dim) → (X dim)) (ψ : P × (X dim) → ℝ) (q : P × (X dim)) : ℝ :=
  ψ q * conormalComponent (fun w => g (q.1,w)) q.2 (V q)

@[expose] def velocityRotationDatum
    (g : P × (X dim) → (Mat dim)) (V : P × (X dim) → (X dim)) (ψ : P × (X dim) → ℝ)
    (i j : (I dim)) (q : P × (X dim)) : ℝ :=
  ψ q * (q.2 i * tangentialComponent (fun w => g (q.1,w)) q.2 (V q) j)

/-- The angular adjoint of a velocity, with its harmonic normal
contribution and its tangential integration-by-parts terms. -/
@[expose] def parametricBallVelocityAdjoint
    (g : P × (X dim) → (Mat dim)) (V : P × (X dim) → (X dim)) (ψ : P × (X dim) → ℝ) (q : P × (X dim)) : ℝ :=
  parametricBallConormal g (velocityBoundaryDatum g V ψ) q -
    ∑ i, ∑ j, sphereRotationDerivative i j
      (fun z => velocityRotationDatum g V ψ i j (q.1,z)) (sphereNormalize q.2)

end CalderonN
