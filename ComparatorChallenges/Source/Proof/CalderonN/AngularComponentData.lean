module

public import Proof.CalderonN.PhysicalAngularModelData
public import Proof.CalderonN.AngularOutputSections
import Mathlib.Tactic
public import Proof.CalderonN.SmoothHarmonicWeights
public import Proof.CalderonN.SphereFrame
public import Proof.CalderonN.FischerFields
import Mathlib.Tactic.Ring
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
public import Proof.CalderonN.MetricDensity
import Mathlib.Analysis.Calculus.ContDiff.WithLp
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
import Mathlib.Tactic.GCongr
public import Proof.CalderonN.ZonalProjection
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
public import Proof.CalderonN.GaussianSphere
import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Proof.CalderonN.Coordinates
public import Proof.CalderonN.HarmonicTestExpansion
public import Proof.CalderonN.SmoothSphereFields

@[expose] public section

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open Set MeasureTheory MvPolynomial Filter
open scoped ContDiff
namespace CalderonN

variable {dim : ℕ} [NeZero dim]
open OAI.AnisotropicCalderon.SphereHarmonic
open OAI.AnisotropicCalderon.SmoothSphereFields

/-- One real linear component of the physical complex model, using the expansion's actual
    harmonic basis and compact support. Real and imaginary components share their radius data. -/
structure AngularComponentData {Y : Set (X dim)} {g : (MetricField dim)} {e : (Frame dim)} {φ : (Field dim)}
    (E : HarmonicTestExpansion Y g e φ) (r : (X dim) → ℝ) (L : ℂ →L[ℝ] ℝ) where
  dimensionBound : 3 ≤ dim
  horizontalRepresentative : (I dim) → (X dim) × (X dim) → ℝ
  horizontalSmooth : ∀ i,ContDiff ℝ ∞ (horizontalRepresentative i)
  horizontalEq : ∀ i,∀ y ∈ Y,∀ v : (UnitSphere dim),horizontalRepresentative i (y,v.val) = L (horizontal g φ y (frameVector e y v.val) (e y i))
  horizontalZero : ∀ i,∀ y ∉ E.supportSet,∀ v : (UnitSphere dim),horizontalRepresentative i (y,v.val) = 0
  coefficient : (I dim) → (X dim) → ℝ
  coefficientSmooth : ∀ i,ContDiff ℝ ∞ (coefficient i)
  coefficientEq : ∀ i,∀ y ∈ E.supportSet,coefficient i y = fderiv ℝ (fun x => Real.log (r x)) y (e y i)
  coordinates : (k : ℕ) → (X dim) → Fin (E.dimension k) → ℝ
  coordinatesSmooth : ∀ k,ContDiff ℝ ∞ (coordinates k)
  coordinatesSupport : ∀ k,tsupport (coordinates k) ⊆ E.supportSet
  coordinatesEq : ∀ k x,polynomialSphereL2 (finitePolynomialField (E.basis k) (coordinates k) x) =
    (harmonicProjection (k+1) (ambientSphereL2 (fun p => L (E.representative p))
      (L.contDiff.comp E.representativeSmooth) x) : (SphereL2 dim))
  zeroDegree : ∀ x,harmonicProjection 0 (ambientSphereL2 (fun p => L (E.representative p))
    (L.contDiff.comp E.representativeSmooth) x) = 0

namespace AngularModelData
variable {Y : Set (X dim)} {g : (MetricField dim)} {e : (Frame dim)} {φ : (Field dim)} {E : HarmonicTestExpansion Y g e φ} {r : (X dim) → ℝ}

/-- Coordinate identity for the real angular component. -/
theorem realComponent_coordinatesEq (k : ℕ) (x : X dim) :
    polynomialSphereL2 (finitePolynomialField (E.basis k) (E.realCoefficients k) x) =
      (harmonicProjection (k + 1)
        (ambientSphereL2 (fun p => Complex.reCLM (E.representative p))
          (Complex.reCLM.contDiff.comp E.representativeSmooth) x)).val := sorry

/-- Zero-mode identity for the real angular component. -/
theorem realComponent_zeroDegree (x : X dim) :
    harmonicProjection 0
      (ambientSphereL2 (fun p => Complex.reCLM (E.representative p))
        (Complex.reCLM.contDiff.comp E.representativeSmooth) x) = 0 := sorry

def realComponent (D : AngularModelData E r) : AngularComponentData E r Complex.reCLM where
  dimensionBound := D.dimensionBound
  horizontalRepresentative := D.realHorizontal
  horizontalSmooth := D.realSmooth
  horizontalEq := by intro i y hy v; simpa only [Complex.reCLM_apply] using D.realEq i y hy v
  horizontalZero := D.realZero
  coefficient := D.coefficient
  coefficientSmooth := D.coefficientSmooth
  coefficientEq := D.coefficientEq
  coordinates := E.realCoefficients
  coordinatesSmooth := E.realSmooth
  coordinatesSupport := E.realSupport
  coordinatesEq := realComponent_coordinatesEq
  zeroDegree := realComponent_zeroDegree

/-- Coordinate identity for the imag angular component. -/
theorem imagComponent_coordinatesEq (k : ℕ) (x : X dim) :
    polynomialSphereL2 (finitePolynomialField (E.basis k) (E.imagCoefficients k) x) =
      (harmonicProjection (k + 1)
        (ambientSphereL2 (fun p => Complex.imCLM (E.representative p))
          (Complex.imCLM.contDiff.comp E.representativeSmooth) x)).val := sorry

/-- Zero-mode identity for the imag angular component. -/
theorem imagComponent_zeroDegree (x : X dim) :
    harmonicProjection 0
      (ambientSphereL2 (fun p => Complex.imCLM (E.representative p))
        (Complex.imCLM.contDiff.comp E.representativeSmooth) x) = 0 := sorry

def imagComponent (D : AngularModelData E r) : AngularComponentData E r Complex.imCLM where
  dimensionBound := D.dimensionBound
  horizontalRepresentative := D.imagHorizontal
  horizontalSmooth := D.imagSmooth
  horizontalEq := by intro i y hy v; simpa only [Complex.imCLM_apply] using D.imagEq i y hy v
  horizontalZero := D.imagZero
  coefficient := D.coefficient
  coefficientSmooth := D.coefficientSmooth
  coefficientEq := D.coefficientEq
  coordinates := E.imagCoefficients
  coordinatesSmooth := E.imagSmooth
  coordinatesSupport := E.imagSupport
  coordinatesEq := imagComponent_coordinatesEq
  zeroDegree := imagComponent_zeroDegree

end AngularModelData

namespace AngularComponentData
variable {Y : Set (X dim)} {g : (MetricField dim)} {e : (Frame dim)} {φ : (Field dim)} {E : HarmonicTestExpansion Y g e φ}
  {r : (X dim) → ℝ} {L : ℂ →L[ℝ] ℝ}

def raisingOutput (Q : AngularComponentData E r L) : (X dim) → (SphereL2 dim) :=
  angularRaisingSum Q.dimensionBound Q.horizontalRepresentative (fun p => L (E.representative p)) Q.horizontalSmooth
    (L.contDiff.comp E.representativeSmooth) Q.coefficient

def loweringOutput (Q : AngularComponentData E r L) : (X dim) → (SphereL2 dim) :=
  angularLoweringSum Q.dimensionBound Q.horizontalRepresentative (fun p => L (E.representative p)) Q.horizontalSmooth
    (L.contDiff.comp E.representativeSmooth) Q.coefficient

end AngularComponentData
end CalderonN
