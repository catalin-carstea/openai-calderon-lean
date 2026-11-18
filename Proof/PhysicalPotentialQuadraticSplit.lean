import Proof.PhysicalBalancedPotential
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2600000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
open Set
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.SphereHarmonic

/-- The single-degree part of the actual model potential. -/
def principalModelPotentialLinearHalfL (d : Data) (y : X) :
    SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ)) :=
  ∑ i : I,∑ j : I,frameTensorMatrix d.γ d.frame y (principal d.γ d.g₂ y) i j •
    ((d.radius y*hessianBilinear d.γ (fun x => Real.log (d.radius x)) y (d.frame y i) (d.frame y j)) •
      (sphereSobolevShiftedDegreeL (1/2:ℝ)).comp (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)))

/-- The degree/degree and raising/degree words of the same model potential. -/
def principalModelPotentialQuadraticHalfL (d : Data) (y : X) :
    SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ)) :=
  let q := frameTensorMatrix d.γ d.frame y (principal d.γ d.g₂ y)
  let f := fun k => fderiv ℝ (fun x => Real.log (d.radius x)) y (d.frame y k)
  (∑ i : I,∑ j : I,q i j • ((d.radius y*f i*f j) •
      (sphereSobolevShiftedDegreeL (1/2:ℝ)).comp (sphereSobolevShiftedDegreeL (3/2:ℝ))))+
    (2:ℝ) • (∑ i : I,∑ j : I,((q i j-(if i=j then 1 else 0))*f j) •
      (flatHalfRaisingL i).comp (sphereSobolevShiftedDegreeL (3/2:ℝ)))

lemma principalModelPotentialHalfL_linear_quadratic (d : Data) (y : X) :
    principalModelPotentialHalfL d y=
      principalModelPotentialLinearHalfL d y+principalModelPotentialQuadraticHalfL d y := by
  simp only [principalModelPotentialHalfL,principalModelPotentialLinearHalfL,
    principalModelPotentialQuadraticHalfL,smul_add,Finset.sum_add_distrib]
  abel

namespace PhysicalPrincipalData
variable {Y : Set X} {d : Data} {CF CT : ℝ}

/-- All genuine quadratic degree/raising/first-error words in the full
    zero-base physical coefficient, retaining every mixed contribution. -/
def potentialQuadraticHalfL (P : PhysicalPrincipalData Y d CF CT) (y : X) :
    SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ)) :=
  principalModelPotentialQuadraticHalfL d y+pureAngularPrincipalHalfL d y+
    P.first.principalRaisingCrossL y+P.first.principalDegreeCrossL y+P.first.radiusPrincipalProductL y

/-- The complete complementary part. These terms are kept explicit for
    their genuine order-one lifts and covariant estimates. -/
def potentialRemainderHalfL (P : PhysicalPrincipalData Y d CF CT) (y : X) :
    SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ)) :=
  principalModelPotentialLinearHalfL d y+
    balancedCoarsePotentialL (principalCovariantPotentialL d P.tensor y)+
    balancedCoarsePotentialL (principalRaisingCorrectionPerturbationL d y)+
    balancedCoarsePotentialL (principalDegreeCorrectionCrossL d y)+
    balancedCoarsePotentialL ((principalCorrectionProductL 0 d y).comp
      (sphereSobolevInclusionL 1 0 (by norm_num)))+P.first.principalCorrectionCrossL y

/-- Exact full potential split on its genuine balanced domains. The
    remainder is neither omitted nor assumed small by this algebraic lemma. -/
lemma remainingPotentialHalfL_quadratic_remainder (P : PhysicalPrincipalData Y d CF CT) (y : X) :
    P.remainingPotentialHalfL y=P.potentialQuadraticHalfL y+P.potentialRemainderHalfL y := by
  rw [remainingPotentialHalfL,principalModelPotentialHalfL_linear_quadratic]
  unfold potentialQuadraticHalfL potentialRemainderHalfL
  abel
end PhysicalPrincipalData
end ShrinkingSpheres
