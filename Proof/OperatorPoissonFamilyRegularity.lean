import Proof.CommonSupportPoissonRegularity
import Proof.StrongPoissonTaylor

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1400000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set
open scoped ContDiff
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.EnergyBridge OAI.AnisotropicCalderon.DirichletFamily
attribute [local irreducible] strongCoefficientOperatorL fullCoefficientOperatorL

variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]

/-- The native Poisson family is smooth whenever its genuine full and strong
    operators are smooth and the actual strong Dirichlet maps are invertible.
    This permits affine-assembled coefficient families with shared Taylor data. -/
theorem contDiffOn_strongPoissonL_of_operators
    (F : P → SmoothCoefficientMatrix 2) (U : Set P)
    (hA : ContDiffOn ℝ ∞ (fun p => strongDirichletOperator fixedSobolevCalculus 0 (F p)) U)
    (hT : ContDiffOn ℝ ∞ (fun p => fullCoefficientOperatorL fixedSobolevCalculus 0 (F p)) U)
    (hInv : ∀ p ∈ U,(strongDirichletOperator fixedSobolevCalculus 0 (F p)).IsInvertible) :
    ContDiffOn ℝ ∞ (fun p => strongPoissonL (F p)) U := by
  have hi := contDiffOn_banachInverseFamily _ U hA hInv
  have hc : ContDiffOn ℝ ∞ (fun p => fixedStrongH2InclusionL.comp
      ((strongDirichletOperator fixedSobolevCalculus 0 (F p)).inverse.comp
        (fullCoefficientOperatorL fixedSobolevCalculus 0 (F p)))) U :=
    contDiffOn_const.clm_comp (hi.clm_comp hT)
  change ContDiffOn ℝ ∞ (fun p => ((ContinuousLinearMap.id ℝ (BallSobolev 2))-
    fixedStrongH2InclusionL.comp ((strongDirichletOperator fixedSobolevCalculus 0 (F p)).inverse.comp
      (fullCoefficientOperatorL fixedSobolevCalculus 0 (F p)))).comp fixedHarmonicLiftL) U
  exact (contDiffOn_const.sub hc).clm_comp contDiffOn_const

theorem contDiffOn_actualHighRadialErrorL_of_operators
    (F : P → SmoothCoefficientMatrix 2) (U : Set P)
    (hA : ContDiffOn ℝ ∞ (fun p => strongDirichletOperator fixedSobolevCalculus 0 (F p)) U)
    (hT : ContDiffOn ℝ ∞ (fun p => fullCoefficientOperatorL fixedSobolevCalculus 0 (F p)) U)
    (hInv : ∀ p ∈ U,(strongDirichletOperator fixedSobolevCalculus 0 (F p)).IsInvertible) :
    ContDiffOn ℝ ∞ (fun p => actualHighRadialErrorL (F p)) U :=
  (contDiffOn_const.clm_comp (contDiffOn_strongPoissonL_of_operators F U hA hT hInv)).sub contDiffOn_const

/-- A genuine fixed-center first Poisson variation family is smooth through
    its actual full coefficient operator; no derivative witness is substituted. -/
theorem contDiffOn_highFirstRadialVariationL_of_operator
    (F1 : P → SmoothCoefficientMatrix 2) (F0 : SmoothCoefficientMatrix 2) (c : ℝ) (U : Set P)
    (hT1 : ContDiffOn ℝ ∞ (fun p => fullCoefficientOperatorL fixedSobolevCalculus 0 (F1 p)) U) :
    ContDiffOn ℝ ∞ (fun p => highFirstRadialVariationL F0 (F1 p) c) U := by
  have hFirst : ContDiffOn ℝ ∞ (fun p => strongFirstPoissonVariationL F0 (F1 p) c) U :=
    (contDiffOn_const.clm_comp (contDiffOn_const.clm_comp (hT1.clm_comp contDiffOn_const))).neg
  exact contDiffOn_const.clm_comp hFirst

end ShrinkingSpheres
