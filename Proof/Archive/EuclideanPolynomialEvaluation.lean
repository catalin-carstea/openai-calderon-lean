/- Adopted from the selected ZIP, lean/Calderon/GreenEuclidean.lean.
   Initial Euclidean evaluation and Frechet derivative lemmas only; proof bodies preserved, local imports narrowed.
-/
import Proof.Archive.PolynomialEvaluation
import Proof.Archive.SphereHarmonicBridge
import Mathlib.Analysis.InnerProductSpace.PiL2
noncomputable section
namespace OAI.AnisotropicCalderon.GreenRadialTrace
open MvPolynomial AngularPolynomial SphereHarmonic

def euclideanCoordinates : R3 ≃L[ℝ] (Fin 3 → ℝ) :=
  PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)

def polynomialEvaluation (p : MvPolynomial (Fin 3) ℝ) (x : R3) : ℝ :=
  eval (euclideanCoordinates x) p

theorem hasFDerivAt_polynomialEvaluation (p : MvPolynomial (Fin 3) ℝ) (x : R3) :
    HasFDerivAt (polynomialEvaluation p)
      ((polynomialFDeriv p (euclideanCoordinates x)).comp
        euclideanCoordinates.toContinuousLinearMap) x := by
  exact (hasFDerivAt_eval p (euclideanCoordinates x)).comp x
    euclideanCoordinates.toContinuousLinearMap.hasFDerivAt

theorem fderiv_polynomialEvaluation_apply (p : MvPolynomial (Fin 3) ℝ) (x v : R3) :
    fderiv ℝ (polynomialEvaluation p) x v =
      ∑ i : Fin 3, v i * polynomialEvaluation (pderiv i p) x := by
  rw [(hasFDerivAt_polynomialEvaluation p x).fderiv]
  exact polynomialFDeriv_apply p (euclideanCoordinates x) (euclideanCoordinates v)

theorem fderiv_polynomialEvaluation_eq_coordinate (p : MvPolynomial (Fin 3) ℝ) (x v : R3) :
    fderiv ℝ (polynomialEvaluation p) x v =
      fderiv ℝ (fun z : Fin 3 → ℝ => eval z p)
        (euclideanCoordinates x) (euclideanCoordinates v) := by
  rw [(hasFDerivAt_polynomialEvaluation p x).fderiv,
    (hasFDerivAt_eval p (euclideanCoordinates x)).fderiv]
  rfl


end OAI.AnisotropicCalderon.GreenRadialTrace
