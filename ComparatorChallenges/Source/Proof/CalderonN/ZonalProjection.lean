module

public import Proof.CalderonN.GaussianSphere
public import Proof.Archive.AngularCoefficient
public import Proof.CalderonN.Coercivity
import Mathlib.Tactic
public import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
public import Proof.CalderonN.Coordinates
public import Proof.CalderonN.SphereHarmonicBridge

@[expose] public section

/- Port of the pointwise projector comparison from Proposition 5.3 check f308cb9d.
   The finite-dimensional harmonic subspace admits an orthogonal projection directly. -/
noncomputable section
open MeasureTheory MvPolynomial
open scoped InnerProductSpace

namespace CalderonN
open OAI.AnisotropicCalderon.AngularPolynomial
open OAI.AnisotropicCalderon.SphereHarmonic

variable {n : ℕ}

variable [NeZero n]

instance (k : ℕ) : FiniteDimensional ℝ (harmonicSphereSubspace n k) := sorry

def harmonicProjection (k : ℕ) : SphereL2 n →L[ℝ] harmonicSphereSubspace n k :=
  (harmonicSphereSubspace n k).orthogonalProjectionOnto

end CalderonN
