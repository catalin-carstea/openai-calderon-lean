module

public import Proof.Archive.PolynomialEvaluation
public import Proof.CalderonN.SphereHarmonicBridge
public import Mathlib.Analysis.InnerProductSpace.PiL2

@[expose] public section

/- Adopted from the selected ZIP, lean/Calderon/GreenEuclidean.lean.
   Initial Euclidean evaluation and Frechet derivative lemmas only; proof bodies preserved, local imports narrowed.
-/
noncomputable section
namespace OAI.AnisotropicCalderon.GreenRadialTrace
open MvPolynomial AngularPolynomial SphereHarmonic

variable {n : ℕ}

def euclideanCoordinates (n : ℕ) : (CalderonN.X n) ≃L[ℝ] (Fin n → ℝ) :=
  PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin n => ℝ)

def polynomialEvaluation (p : MvPolynomial (Fin n) ℝ) (x : (CalderonN.X n)) : ℝ :=
  eval (euclideanCoordinates n x) p

theorem hasFDerivAt_polynomialEvaluation (p : MvPolynomial (Fin n) ℝ) (x : (CalderonN.X n)) :
    HasFDerivAt (polynomialEvaluation p)
      ((polynomialFDeriv p (euclideanCoordinates n x)).comp
        (euclideanCoordinates n).toContinuousLinearMap) x := by
  exact (hasFDerivAt_eval p (euclideanCoordinates n x)).comp x
    ((euclideanCoordinates n).toContinuousLinearMap.hasFDerivAt)

theorem fderiv_polynomialEvaluation_apply (p : MvPolynomial (Fin n) ℝ) (x v : (CalderonN.X n)) :
    fderiv ℝ (polynomialEvaluation p) x v =
      ∑ i : Fin n, v i * polynomialEvaluation (pderiv i p) x := by
  rw [(hasFDerivAt_polynomialEvaluation p x).fderiv]
  exact polynomialFDeriv_apply p (euclideanCoordinates n x) (euclideanCoordinates n v)

theorem fderiv_polynomialEvaluation_eq_coordinate (p : MvPolynomial (Fin n) ℝ) (x v : (CalderonN.X n)) :
    fderiv ℝ (polynomialEvaluation p) x v =
      fderiv ℝ (fun z : Fin n → ℝ => eval z p)
        (euclideanCoordinates n x) (euclideanCoordinates n v) := by
  rw [(hasFDerivAt_polynomialEvaluation p x).fderiv,
    (hasFDerivAt_eval p (euclideanCoordinates n x)).fderiv]
  rfl


end OAI.AnisotropicCalderon.GreenRadialTrace
