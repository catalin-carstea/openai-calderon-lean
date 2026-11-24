module

public import Proof.CalderonN.AngularComponentData
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
public import Proof.CalderonN.ZonalProjection
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
public import Proof.CalderonN.GaussianSphere
import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Proof.CalderonN.HarmonicHilbertDecomposition
import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Proof.CalderonN.Coordinates
public import Proof.CalderonN.HarmonicTestExpansion
public import Proof.CalderonN.PhysicalAngularModelData
public import Proof.CalderonN.SphereHarmonicBridge

@[expose] public section

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open Set MeasureTheory Filter
open scoped ContDiff Topology
namespace CalderonN

variable {dim : ℕ} [NeZero dim]
open OAI.AnisotropicCalderon.SphereHarmonic

namespace AngularComponentData
variable {Y : Set (X dim)} {g : (MetricField dim)} {e : (Frame dim)} {φ : (Field dim)} {E : HarmonicTestExpansion Y g e φ}
  {r : (X dim) → ℝ} {L : ℂ →L[ℝ] ℝ}

end AngularComponentData

namespace AngularModelData
variable {Y : Set (X dim)} {g : (MetricField dim)} {e : (Frame dim)} {φ : (Field dim)} {E : HarmonicTestExpansion Y g e φ} {r : (X dim) → ℝ}

def raisingSquare (D : AngularModelData E r) : ℝ :=
  (∫ y in Y,metricDensity g y*‖D.realComponent.raisingOutput y‖^2)+
    (∫ y in Y,metricDensity g y*‖D.imagComponent.raisingOutput y‖^2)

def loweringSquare (D : AngularModelData E r) : ℝ :=
  (∫ y in Y,metricDensity g y*‖D.realComponent.loweringOutput y‖^2)+
    (∫ y in Y,metricDensity g y*‖D.imagComponent.loweringOutput y‖^2)

end AngularModelData
end CalderonN
