import Proof.PhysicalPotentialQuadraticSplit
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2600000
set_option maxSynthPendingDepth 30
set_option maxRecDepth 2400
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
open Set
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.SphereHarmonic

/-- Degree, the three raising operators, and the SAME three first errors. -/
abbrev PhysicalPotentialGeneratorIndex := Unit ⊕ (I ⊕ I)

namespace PhysicalPrincipalData
variable {Y : Set X} {d : Data} {CF CT : ℝ}

def potentialGeneratorLow (P : PhysicalPrincipalData Y d CF CT) (y : X) :
    PhysicalPotentialGeneratorIndex → SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ))
  | .inl _ => sphereSobolevShiftedDegreeL (1/2:ℝ)
  | .inr (.inl i) => flatHalfRaisingL i
  | .inr (.inr i) => P.first.low i y

def potentialGeneratorHigh (P : PhysicalPrincipalData Y d CF CT) (y : X) :
    PhysicalPotentialGeneratorIndex → SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ)
  | .inl _ => sphereSobolevShiftedDegreeL (3/2:ℝ)
  | .inr (.inl i) => flatThreeHalfRaisingL i
  | .inr (.inr i) => P.first.high i y

def potentialWordCoefficient (d : Data) (y : X) :
    PhysicalPotentialGeneratorIndex → PhysicalPotentialGeneratorIndex → ℝ
  | .inl _, .inl _ => ∑ i : I,∑ j : I,frameTensorMatrix d.γ d.frame y (principal d.γ d.g₂ y) i j*
      (d.radius y*fderiv ℝ (fun x => Real.log (d.radius x)) y (d.frame y i)*
        fderiv ℝ (fun x => Real.log (d.radius x)) y (d.frame y j))
  | .inl _, .inr (.inl _) => 0
  | .inl _, .inr (.inr j) => ∑ i : I,frameTensorMatrix d.γ d.frame y (principal d.γ d.g₂ y) i j*
      scaledFrameLogRadius d.radius d.frame i y
  | .inr (.inl i), .inl _ => 2*∑ j : I,
      (frameTensorMatrix d.γ d.frame y (principal d.γ d.g₂ y) i j-(if i=j then 1 else 0))*
        fderiv ℝ (fun x => Real.log (d.radius x)) y (d.frame y j)
  | .inr (.inl i), .inr (.inl j) =>
      frameTensorMatrix d.γ d.frame y (principal d.γ d.g₂ y-(d.γ y)⁻¹) i j/d.radius y
  | .inr (.inl i), .inr (.inr j) => frameTensorMatrix d.γ d.frame y (principal d.γ d.g₂ y) i j
  | .inr (.inr i), .inl _ => ∑ j : I,frameTensorMatrix d.γ d.frame y (principal d.γ d.g₂ y) i j*
      scaledFrameLogRadius d.radius d.frame j y
  | .inr (.inr i), .inr (.inl j) => frameTensorMatrix d.γ d.frame y (principal d.γ d.g₂ y) i j
  | .inr (.inr i), .inr (.inr j) => d.radius y*frameTensorMatrix d.γ d.frame y (principal d.γ d.g₂ y) i j

def potentialWordMatrixL (P : PhysicalPrincipalData Y d CF CT) (y : X) :
    SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ)) :=
  ∑ a : PhysicalPotentialGeneratorIndex,∑ b : PhysicalPotentialGeneratorIndex,
    potentialWordCoefficient d y a b • (P.potentialGeneratorLow y a).comp (P.potentialGeneratorHigh y b)

/-- Every degree, pure raising, mixed raising/error, mixed degree/error
    and error/error term is included in one finite quadratic word matrix. -/
lemma potentialQuadraticHalfL_eq_word_matrix (P : PhysicalPrincipalData Y d CF CT) (y : X) :
    P.potentialQuadraticHalfL y=P.potentialWordMatrixL y := by
  simp only [potentialWordMatrixL,Fintype.sum_sum_type,Fintype.sum_unique,
    potentialGeneratorLow,potentialGeneratorHigh,potentialWordCoefficient,
    potentialQuadraticHalfL,principalModelPotentialQuadraticHalfL,pureAngularPrincipalHalfL,
    ActualFrameErrorEndpointPair.principalRaisingCrossL,frameErrorMatrixRaisingCrossL,
    ActualFrameErrorEndpointPair.principalDegreeCrossL,frameErrorMatrixDegreeCrossL,
    ActualFrameErrorEndpointPair.radiusPrincipalProductL,ActualFrameErrorEndpointPair.productL,
    ContinuousLinearMap.smul_comp,ContinuousLinearMap.comp_smul,
    smul_add,Finset.smul_sum,Finset.sum_smul,smul_smul,zero_smul,Finset.sum_const_zero,add_zero]
  simp only [Fin.sum_univ_three]
  module

/-- The complete actual potential is the finite word matrix plus its
    explicit complementary coefficient. No cross term is discarded. -/
lemma remainingPotentialHalfL_word_matrix_remainder (P : PhysicalPrincipalData Y d CF CT) (y : X) :
    P.remainingPotentialHalfL y=P.potentialWordMatrixL y+P.potentialRemainderHalfL y := by
  rw [P.remainingPotentialHalfL_quadratic_remainder,P.potentialQuadraticHalfL_eq_word_matrix]
end PhysicalPrincipalData
end ShrinkingSpheres
