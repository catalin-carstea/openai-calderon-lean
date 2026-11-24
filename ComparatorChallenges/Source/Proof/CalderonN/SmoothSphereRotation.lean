module

public import Proof.CalderonN.SphereHarmonicBridge
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
public import Mathlib.Analysis.Calculus.ParametricIntegral
public import Mathlib.Analysis.Calculus.ContDiff.WithLp
public import Mathlib.Analysis.Calculus.FDeriv.WithLp
public import Mathlib.Analysis.Calculus.Deriv.Prod
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
public import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.Tactic
public import Proof.CalderonN.Coordinates

@[expose] public section

/- Adopted from the selected ZIP, lean/Calderon/SmoothSphereRotation.lean.
   Complete generic module; proof bodies preserved, local imports rewritten.
-/
set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter
open scoped ContDiff Topology ENNReal
namespace OAI.AnisotropicCalderon.SmoothSphereRotation
open SphereHarmonic

variable {n : ℕ}


def coordinateRotation (i j : Fin n) (t : ℝ) (x : (CalderonN.X n)) : (CalderonN.X n) :=
  if i = j then x else WithLp.toLp 2 fun l =>
    if l = i then Real.cos t * x i - Real.sin t * x j else
    if l = j then Real.sin t * x i + Real.cos t * x j else x l


def rotationVector (i j : Fin n) (x : (CalderonN.X n)) : (CalderonN.X n) :=
  x i • PiLp.single 2 j (1 : ℝ) - x j • PiLp.single 2 i (1 : ℝ)

def sphereRotationDerivative (i j : Fin n) (F : (CalderonN.X n) → ℝ) (x : (CalderonN.X n)) : ℝ :=
  fderiv ℝ F x (rotationVector i j x)

variable [NeZero n]





end OAI.AnisotropicCalderon.SmoothSphereRotation
