module

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
public import Proof.CalderonN.ZonalProjection
public import Proof.CalderonN.MetricDensity
import Mathlib.Analysis.Calculus.ContDiff.WithLp
public import Proof.CalderonN.MetricConnection
import Mathlib.Analysis.Normed.Operator.NormedSpace
public import Proof.Archive.AngularCoefficient
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Trace
public import Proof.Archive.FischerPolynomial
public import Mathlib.Analysis.Calculus.FDeriv.Prod
public import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Algebra.MvPolynomial.Funext
public import Proof.CalderonN.SmoothSphereFields
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.GCongr
public import Proof.CalderonN.GaussianSphere
import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Proof.CalderonN.SmoothSphereRotationProjection
public import Proof.CalderonN.FramePullback
public import Proof.CalderonN.SmoothAmbientAngularCasimir
public import Proof.CalderonN.Coordinates
public import Proof.CalderonN.MovingTrace

@[expose] public section

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open Set MeasureTheory MvPolynomial Filter
open scoped ContDiff
namespace CalderonN
variable {N : ℕ} [NeZero N]
open OAI.AnisotropicCalderon.SphereHarmonic
open OAI.AnisotropicCalderon.SmoothSphereFields

/-- Shared genuine harmonic coordinates of one actual test. The same smooth representative,
    compact support and real/imaginary bases are used by all cutoffs and graph limits. -/
structure HarmonicTestExpansion (Y : Set (X N)) (g : (MetricField N)) (e : (Frame N)) (φ : (Field N)) where
  supportSet : Set (X N)
  compactSupportSet : IsCompact supportSet
  supportSubset : supportSet ⊆ Y
  representative : (Field N)
  representativeSmooth : ContDiff ℝ ∞ representative
  representativeEq : ∀ y ∈ Y,∀ v : (UnitSphere N),representative (y,v.val) = φ (y,frameVector e y v.val)
  representativeZero : ∀ y ∉ supportSet,∀ v : (UnitSphere N),representative (y,v.val) = 0
  meanZero : ∀ y ∈ Y,sphereAverage e y (fun w => φ (y,w)) = 0
  dimension : ℕ → ℕ
  basis : (k : ℕ) → Fin (dimension k) → MvPolynomial (I N) ℝ
  basisHarmonic : ∀ k j,basis k j ∈ harmonicHomogeneous N (k+1)
  realCoefficients : (k : ℕ) → (X N) → Fin (dimension k) → ℝ
  imagCoefficients : (k : ℕ) → (X N) → Fin (dimension k) → ℝ
  realSmooth : ∀ k,ContDiff ℝ ∞ (realCoefficients k)
  imagSmooth : ∀ k,ContDiff ℝ ∞ (imagCoefficients k)
  realSupport : ∀ k,tsupport (realCoefficients k) ⊆ supportSet
  imagSupport : ∀ k,tsupport (imagCoefficients k) ⊆ supportSet
  realCoordinates : ∀ k x,polynomialSphereL2 (finitePolynomialField (basis k) (realCoefficients k) x) =
    (harmonicProjection (k+1) (ambientSphereL2 (fun p => (representative p).re)
      (Complex.reCLM.contDiff.comp representativeSmooth) x) : (SphereL2 N))
  imagCoordinates : ∀ k x,polynomialSphereL2 (finitePolynomialField (basis k) (imagCoefficients k) x) =
    (harmonicProjection (k+1) (ambientSphereL2 (fun p => (representative p).im)
      (Complex.imCLM.contDiff.comp representativeSmooth) x) : (SphereL2 N))
  zeroDegreeReal : ∀ x,harmonicProjection 0 (ambientSphereL2 (fun p => (representative p).re)
    (Complex.reCLM.contDiff.comp representativeSmooth) x) = 0
  zeroDegreeImag : ∀ x,harmonicProjection 0 (ambientSphereL2 (fun p => (representative p).im)
    (Complex.imCLM.contDiff.comp representativeSmooth) x) = 0

namespace HarmonicTestExpansion
variable {Y : Set (X N)} {g : (MetricField N)} {e : (Frame N)} {φ : (Field N)}

end HarmonicTestExpansion

end CalderonN
