import Proof.Archive.EuclideanPolynomialEvaluation
import Proof.Archive.MetricDefs
import Mathlib.Analysis.InnerProductSpace.PiL2

noncomputable section
namespace OAI.AnisotropicCalderon.GreenRadialTrace
open MvPolynomial AngularPolynomial

theorem d_polynomialEvaluation (p : MvPolynomial (Fin 3) ℝ) (x : R3) (i : Fin 3) :
    d (polynomialEvaluation p) x i = polynomialEvaluation (pderiv i p) x := by
  classical
  simp [d, fderiv_polynomialEvaluation_apply, PiLp.single_apply]

def euclideanLaplacian (u : R3 → ℝ) (x : R3) : ℝ :=
  ∑ i : Fin 3, d (fun y => d u y i) x i

theorem euclideanLaplacian_polynomialEvaluation (p : MvPolynomial (Fin 3) ℝ) (x : R3) :
    euclideanLaplacian (polynomialEvaluation p) x = polynomialEvaluation (laplacian p) x := by
  classical
  simp only [euclideanLaplacian, d_polynomialEvaluation]
  simp only [polynomialEvaluation, laplacian, map_sum]


end OAI.AnisotropicCalderon.GreenRadialTrace
