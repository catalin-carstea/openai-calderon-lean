module

public import Proof.CalderonN.HarmonicTestExpansion
public import Proof.CalderonN.SmoothHarmonicWeights
public import Proof.CalderonN.SphereFrame
public import Proof.CalderonN.FischerFields
import Mathlib.Tactic.Ring
import Mathlib.Tactic
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
public import Proof.CalderonN.Chart
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Geometry.Manifold.PartitionOfUnity
public import Proof.CalderonN.SphereHarmonicBridge
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Topology.Compactness.SigmaCompact
import Mathlib.Topology.Sets.Opens
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.PSeries
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
public import Proof.CalderonN.FramePullback
public import Proof.CalderonN.MetricDensity
import Mathlib.Analysis.Calculus.ContDiff.WithLp
public import Proof.CalderonN.MetricConnection
import Mathlib.Analysis.Normed.Operator.NormedSpace
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Trace
public import Proof.Archive.AngularCoefficient
public import Proof.Archive.FischerPolynomial
public import Mathlib.Analysis.Calculus.FDeriv.Prod
public import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.GCongr
public import Proof.CalderonN.ZonalProjection
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
public import Proof.CalderonN.GaussianSphere
import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Proof.CalderonN.Coordinates

@[expose] public section

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open Set MeasureTheory Filter
open scoped ContDiff
namespace CalderonN

variable {n : ℕ} [NeZero n]
open OAI.AnisotropicCalderon.SphereHarmonic

namespace HarmonicTestExpansion
variable {Y : Set (X n)} {g : (MetricField n)} {e : (Frame n)} {φ : (Field n)}

end HarmonicTestExpansion

/-- Shared smooth real and imaginary horizontal representatives and localized logarithmic
    radius coefficients for one canonical test expansion. They use its one compact support. -/
structure AngularModelData {Y : Set (X n)} {g : (MetricField n)} {e : (Frame n)} {φ : (Field n)}
    (E : HarmonicTestExpansion Y g e φ) (r : (X n) → ℝ) where
  dimensionBound : 3 ≤ n
  realHorizontal : (I n) → (X n) × (X n) → ℝ
  imagHorizontal : (I n) → (X n) × (X n) → ℝ
  realSmooth : ∀ i,ContDiff ℝ ∞ (realHorizontal i)
  imagSmooth : ∀ i,ContDiff ℝ ∞ (imagHorizontal i)
  realEq : ∀ i,∀ y ∈ Y,∀ v : (UnitSphere n),realHorizontal i (y,v.val) = (horizontal g φ y (frameVector e y v.val) (e y i)).re
  imagEq : ∀ i,∀ y ∈ Y,∀ v : (UnitSphere n),imagHorizontal i (y,v.val) = (horizontal g φ y (frameVector e y v.val) (e y i)).im
  realZero : ∀ i,∀ y ∉ E.supportSet,∀ v : (UnitSphere n),realHorizontal i (y,v.val) = 0
  imagZero : ∀ i,∀ y ∉ E.supportSet,∀ v : (UnitSphere n),imagHorizontal i (y,v.val) = 0
  coefficient : (I n) → (X n) → ℝ
  coefficientSmooth : ∀ i,ContDiff ℝ ∞ (coefficient i)
  coefficientEq : ∀ i,∀ y ∈ E.supportSet,coefficient i y = fderiv ℝ (fun x => Real.log (r x)) y (e y i)

end CalderonN
