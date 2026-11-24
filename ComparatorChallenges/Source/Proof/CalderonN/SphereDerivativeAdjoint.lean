module

public import Proof.CalderonN.SmoothSphereRotationProjection
public import Proof.CalderonN.MetricDensity
import Mathlib.Analysis.Calculus.ContDiff.WithLp
import Mathlib.Tactic
public import Proof.CalderonN.FischerFields
public import Proof.CalderonN.SphereFrame
import Mathlib.Tactic.Ring
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
public import Proof.CalderonN.Chart
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Trace
public import Proof.Archive.AngularCoefficient
public import Proof.CalderonN.MetricConnection
import Mathlib.Analysis.Normed.Operator.NormedSpace
public import Proof.Archive.FischerPolynomial
public import Mathlib.Analysis.Calculus.FDeriv.Prod
public import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.GCongr
public import Proof.CalderonN.SphereHarmonicBridge

@[expose] public section

/- Adapted from SphereElementaryCore and SphereDerivativeAdjoint in
   Proposition 5.3 release f308cb9d. -/
noncomputable section
open MvPolynomial
open scoped InnerProductSpace

namespace CalderonN

open OAI.AnisotropicCalderon SphereHarmonic AngularPolynomial

variable {n : ℕ} [NeZero n]

lemma pderiv_harmonicHomogeneous_succ (m : ℕ) (i : Fin n)
    (h : MvPolynomial (Fin n) ℝ) (hh : h ∈ harmonicHomogeneous n (m + 1)) :
    pderiv i h ∈ harmonicHomogeneous n m := sorry

end CalderonN
