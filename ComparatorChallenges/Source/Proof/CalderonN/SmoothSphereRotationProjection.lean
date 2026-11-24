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
public import Proof.CalderonN.Coordinates

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 1200000
noncomputable section
open MeasureTheory MvPolynomial
open scoped ContDiff Topology ENNReal InnerProductSpace
namespace CalderonN
open OAI.AnisotropicCalderon AngularPolynomial SphereHarmonic SmoothSphereRotation
variable {n : ℕ} [NeZero n]






def harmonicPolynomialSphereMap (k : ℕ) :
    harmonicHomogeneous n k →ₗ[ℝ] harmonicSphereSubspace n k :=
  ((polynomialSphereL2 (n := n)).comp (harmonicHomogeneous n k).subtype).codRestrict
    (harmonicSphereSubspace n k) (fun p => Submodule.mem_map_of_mem p.property)

lemma harmonicPolynomialSphereMap_surjective (k : ℕ) :
    Function.Surjective (harmonicPolynomialSphereMap (n := n) k) := sorry









end CalderonN
