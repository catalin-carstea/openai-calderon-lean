import Proof.LocalCoefficientOperatorCongruence
import Proof.StrongPoissonTaylorDerivative

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.EnergyBridge OAI.AnisotropicCalderon.DirichletFamily
attribute [local irreducible] fullCoefficientOperatorL strongCoefficientOperatorL

/-- The actual native strong Poisson map is independent of the coefficient
    representative outside the physical open ball. -/
theorem strongPoissonL_eq_of_unitBall (F G : SmoothCoefficientMatrix 2)
    (hField : ∀ z ∈ (ballOpens:Set X),coefficientMatrixField 2 F z = coefficientMatrixField 2 G z) :
    strongPoissonL F = strongPoissonL G := by
  obtain ⟨hS,hT⟩ := coefficientOperators_eq_of_unitBall fixedSobolevCalculus F G hField
  apply ContinuousLinearMap.ext
  intro f
  change fixedHarmonicLiftL f-fixedStrongH2InclusionL
      ((strongDirichletOperator fixedSobolevCalculus 0 F).inverse
        (fullCoefficientOperatorL fixedSobolevCalculus 0 F (fixedHarmonicLiftL f))) =
    fixedHarmonicLiftL f-fixedStrongH2InclusionL
      ((strongDirichletOperator fixedSobolevCalculus 0 G).inverse
        (fullCoefficientOperatorL fixedSobolevCalculus 0 G (fixedHarmonicLiftL f)))
  rw [hS,hT]

/-- The true first Poisson variation uses only the scalar-center operator
    and affine coefficient on the unit ball, regardless of their cutoffs. -/
theorem strongFirstPoissonVariationL_eq_of_unitBall
    (F0 G0 F1 G1 : SmoothCoefficientMatrix 2) (c : ℝ)
    (h0 : ∀ z ∈ (ballOpens:Set X),coefficientMatrixField 2 F0 z = coefficientMatrixField 2 G0 z)
    (h1 : ∀ z ∈ (ballOpens:Set X),coefficientMatrixField 2 F1 z = coefficientMatrixField 2 G1 z) :
    strongFirstPoissonVariationL F0 F1 c = strongFirstPoissonVariationL G0 G1 c := by
  have hScalar : ∀ z ∈ (ballOpens:Set X),coefficientMatrixField 2 (c • F0) z =
      coefficientMatrixField 2 (c • G0) z := by
    intro z hz
    rw [coefficientMatrixField_smul,coefficientMatrixField_smul,h0 z hz]
  have hS := (coefficientOperators_eq_of_unitBall fixedSobolevCalculus (c • F0) (c • G0) hScalar).1
  have hT := (coefficientOperators_eq_of_unitBall fixedSobolevCalculus F1 G1 h1).2
  unfold strongFirstPoissonVariationL
  rw [hS,hT]

/-- Uniform pointwise bulk Taylor estimates can be transferred to the same
    genuine angle-family witnesses used in derivative estimates. -/
theorem strongPoisson_first_remainder_eq_of_unitBall
    (F G F0 G0 F1 G1 : SmoothCoefficientMatrix 2) (c r : ℝ)
    (h : ∀ z ∈ (ballOpens:Set X),coefficientMatrixField 2 F z = coefficientMatrixField 2 G z)
    (h0 : ∀ z ∈ (ballOpens:Set X),coefficientMatrixField 2 F0 z = coefficientMatrixField 2 G0 z)
    (h1 : ∀ z ∈ (ballOpens:Set X),coefficientMatrixField 2 F1 z = coefficientMatrixField 2 G1 z) :
    strongPoissonL F-fixedHarmonicLiftL-r • strongFirstPoissonVariationL F0 F1 c =
      strongPoissonL G-fixedHarmonicLiftL-r • strongFirstPoissonVariationL G0 G1 c := by
  rw [strongPoissonL_eq_of_unitBall F G h,strongFirstPoissonVariationL_eq_of_unitBall F0 G0 F1 G1 c h0 h1]

end ShrinkingSpheres
