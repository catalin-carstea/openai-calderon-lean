import Proof.StrongPoissonPerturbation
import Proof.ActualHighRadialEndpoint
import Proof.RadialEndpointCompatibility
import Proof.Archive.SmoothCommonSupportStrongOperator

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1400000
set_option maxSynthPendingDepth 20
open Set
open scoped ContDiff Matrix.Norms.Elementwise
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.EnergyBridge OAI.AnisotropicCalderon.DirichletFamily
open OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]

/-- The full divergence operator depends smoothly on an actual common-support
    matrix family, through the supplied closed coefficient multiplier calculus. -/
lemma contDiff_commonSupport_fullCoefficientOperator (s : ℕ)
    (a : P × X → Mat) (ha : ContDiff ℝ ∞ a) (S : Set X) (hS : IsCompact S)
    (hz : ∀ p z,z ∉ S → a (p,z) = 0) :
    ContDiff ℝ ∞ (fun p => fullCoefficientOperatorL fixedSobolevCalculus s
      (commonSupportMatrixFamily (s+2) a ha S hS hz p)) := by
  have hm : ContDiff ℝ ∞ (fun p => coefficientMatrixMultiplierL fixedSobolevCalculus s
      (commonSupportMatrixFamily (s+2) a ha S hS hz p)) := by
    apply contDiff_pi.mpr
    intro i
    apply contDiff_pi.mpr
    intro j
    exact contDiff_commonSupport_actual_coefficientMultiplier fixedSobolevCalculus (s+1)
      (fun q => a q i j) (contDiff_pi.mp (contDiff_pi.mp ha i) j) S hS
      (fun p z h => by rw [hz p z h];rfl)
  exact (coefficientDivergenceL (unitBallCoordinateDerivativeL fixedSobolevCalculus s)
    (unitBallCoordinateDerivativeL fixedSobolevCalculus (s+1))).contDiff.comp hm

/-- Genuine strong Poisson operator families are smooth wherever their actual
    strong Dirichlet operator is invertible. -/
theorem contDiffOn_commonSupport_strongPoissonL
    (a : P × X → Mat) (ha : ContDiff ℝ ∞ a) (S : Set X) (hS : IsCompact S)
    (hz : ∀ p z,z ∉ S → a (p,z) = 0) (V : Set P)
    (hInv : ∀ p ∈ V,(strongDirichletOperator fixedSobolevCalculus 0
      (commonSupportMatrixFamily 2 a ha S hS hz p)).IsInvertible) :
    ContDiffOn ℝ ∞ (fun p => strongPoissonL (commonSupportMatrixFamily 2 a ha S hS hz p)) V := by
  have hStrong := contDiff_commonSupport_actual_strongDirichletOperator fixedSobolevCalculus 0 a ha S hS hz
  have hInverse := contDiffOn_banachInverseFamily _ V hStrong.contDiffOn hInv
  have hFull := contDiff_commonSupport_fullCoefficientOperator 0 a ha S hS hz
  have hCorrection : ContDiffOn ℝ ∞ (fun p => fixedStrongH2InclusionL.comp
      ((strongDirichletOperator fixedSobolevCalculus 0
        (commonSupportMatrixFamily 2 a ha S hS hz p)).inverse.comp
          (fullCoefficientOperatorL fixedSobolevCalculus 0
            (commonSupportMatrixFamily 2 a ha S hS hz p)))) V :=
    contDiffOn_const.clm_comp (hInverse.clm_comp hFull.contDiffOn)
  change ContDiffOn ℝ ∞ (fun p => ((ContinuousLinearMap.id ℝ (BallSobolev 2))-
    fixedStrongH2InclusionL.comp ((strongDirichletOperator fixedSobolevCalculus 0
      (commonSupportMatrixFamily 2 a ha S hS hz p)).inverse.comp
        (fullCoefficientOperatorL fixedSobolevCalculus 0
          (commonSupportMatrixFamily 2 a ha S hS hz p)))).comp fixedHarmonicLiftL) V
  exact (contDiffOn_const.sub hCorrection).clm_comp contDiffOn_const

/-- The actual outward radial response and its high-order error are smooth
    operator families on the same inverse locus. -/
theorem contDiffOn_commonSupport_highRadialErrorL
    (a : P × X → Mat) (ha : ContDiff ℝ ∞ a) (S : Set X) (hS : IsCompact S)
    (hz : ∀ p z,z ∉ S → a (p,z) = 0) (V : Set P)
    (hInv : ∀ p ∈ V,(strongDirichletOperator fixedSobolevCalculus 0
      (commonSupportMatrixFamily 2 a ha S hS hz p)).IsInvertible) :
    ContDiffOn ℝ ∞ (fun p => actualHighRadialErrorL (commonSupportMatrixFamily 2 a ha S hS hz p)) V := by
  have hPoisson := contDiffOn_commonSupport_strongPoissonL a ha S hS hz V hInv
  exact (contDiffOn_const.clm_comp hPoisson).sub contDiffOn_const

end ShrinkingSpheres
