module

public import Proof.CalderonN.CovectorCurvature
public import Proof.CalderonN.FischerCurvatureBound

@[expose] public section

noncomputable section
open MvPolynomial
namespace CalderonN
open OAI.AnisotropicCalderon.AngularPolynomial
variable {n : ℕ}

/- The actual curvature contraction from the checked 3D proof uses the
   general finite-family bound for its frame curvature coefficients. -/
def fullCovectorCurvatureContraction (g : (MetricField n)) (e : Frame n) (y : X n) (p : MvPolynomial (I n) ℝ) : ℝ :=
  ∑ i, ∑ j, fischerInner (pderiv i p)
    (covectorCurvatureAction g e y (e y i) (e y j) (fun a => pderiv a p) j)

theorem fullCovectorCurvatureContraction_bound (g : (MetricField n)) (e : Frame n) (y : X n)
    (B : ℝ) (hB : 0 ≤ B)
    (hR : ∀ i j a b, |frameCurvatureCoefficient g e y (e y i) (e y j) a b| ≤ B)
    {k : ℕ} (hk : 1 ≤ k) (p : MvPolynomial (I n) ℝ) (hp : p.IsHomogeneous k) :
    |fullCovectorCurvatureContraction g e y p| ≤ (n : ℝ)^2*B*(k : ℝ)^2*fischerInner p p :=
  coefficientCurvatureContraction_bound _ B hB hR hk p hp

end CalderonN
