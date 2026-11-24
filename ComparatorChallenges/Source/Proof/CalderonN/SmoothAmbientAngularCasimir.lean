module

public import Proof.CalderonN.SmoothSphereRotation
public import Proof.CalderonN.SphereHarmonicBridge
import Mathlib.Tactic
public import Proof.Archive.FischerPolynomial
public import Mathlib.Analysis.Calculus.FDeriv.Prod
public import Mathlib.Analysis.Calculus.FDeriv.Mul
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Proof.CalderonN.HarmonicHilbertDecomposition
import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Proof.CalderonN.SmoothSphereFields
public import Proof.CalderonN.Coordinates

@[expose] public section

set_option autoImplicit false
noncomputable section
open MeasureTheory Set
open scoped ContDiff Topology ENNReal

namespace CalderonN

variable {N : ℕ} [NeZero N]
open OAI.AnisotropicCalderon SphereHarmonic SmoothSphereFields SmoothSphereRotation

def ambientAngularRotation (i j : Fin N) (G : (X N) × (X N) → ℝ) (q : (X N) × (X N)) : ℝ :=
  fderiv ℝ G q (0,rotationVector i j q.2)

def ambientAngularCasimir (G : (X N) × (X N) → ℝ) (q : (X N) × (X N)) : ℝ :=
  -(1/2 : ℝ) * ∑ i : Fin N, ∑ j : Fin N,
    ambientAngularRotation i j (ambientAngularRotation i j G) q

def ambientShiftedAngularCasimir (G : (X N) × (X N) → ℝ) (q : (X N) × (X N)) : ℝ :=
  G q + ambientAngularCasimir G q

lemma contDiff_ambientShiftedAngularCasimir (G : (X N) × (X N) → ℝ) (hG : ContDiff ℝ ∞ G) :
    ContDiff ℝ ∞ (ambientShiftedAngularCasimir G) := sorry



end CalderonN
