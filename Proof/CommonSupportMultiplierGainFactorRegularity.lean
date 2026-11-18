import Proof.CommonSupportWeakFamilyIdentities
import Proof.CommonSupportPoissonRegularity
import Proof.CommonSupportWeakPoissonRegularity

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 4096
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter MeasureTheory
open scoped ContDiff Topology ENNReal Matrix.Norms.Elementwise
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.EnergyBridge OAI.AnisotropicCalderon.DirichletFamily
open OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open OAI.AnisotropicCalderon.SphereHarmonic OAI.AnisotropicCalderon.SpectralCoreRegularity
open OAI.AnisotropicCalderon.NativeCoefficientBoundaryMultiplier
attribute [local instance] TauCeti.W1p0.instNormedAddCommGroup TauCeti.W1p0.instInnerProductSpace
attribute [local irreducible] nativeCoefficientWeakEnergyL nativeZeroCoefficientEnergyL
  nativeCoefficientWeakFunctionalInverse functionalInverse nativeZeroFunctionalInverse
variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]

/-- Shared genuine inverse, coefficient and weak-Poisson factors for
both fixed and moving multiplier families. No multiplier is chosen here. -/
theorem contDiffOn_commonSupport_multiplier_native_factors
    (A A1 : P × X → Mat) (hA : ContDiff ℝ ∞ A) (hA1 : ContDiff ℝ ∞ A1)
    (S S1 : Set X) (hS : IsCompact S) (hS1 : IsCompact S1)
    (hz : ∀ p z,z ∉ S → A (p,z) = 0) (hz1 : ∀ p z,z ∉ S1 → A1 (p,z) = 0)
    (ha : ∀ p,MemLp (fun z => TauCeti.PDE.energyIntegrand
      (coefficientMatrixField 2 (commonSupportMatrixFamily 2 A hA S hS hz p) z) 0 0) ⊤
      ((volume:Measure X).restrict ballOpens))
    (ha1 : ∀ p,MemLp (fun z => TauCeti.PDE.energyIntegrand
      (coefficientMatrixField 2 (commonSupportMatrixFamily 2 A1 hA1 S1 hS1 hz1 p) z) 0 0) ⊤
      ((volume:Measure X).restrict ballOpens))
    (V : Set P)
    (hStrong : ∀ p ∈ V,(strongDirichletOperator fixedSobolevCalculus 0
      (commonSupportMatrixFamily 2 A hA S hS hz p)).IsInvertible)
    (hCoercive : ∀ p ∈ V,IsCoercive (TauCeti.PDE.energyFormH1L0 (commonSupportEnergyMemLp A hA p))) :
    let F := commonSupportMatrixFamily 2 A hA S hS hz
    let F1 := commonSupportMatrixFamily 2 A1 hA1 S1 hS1 hz1
    ContDiffOn ℝ ∞ (fun p => (strongDirichletOperator fixedSobolevCalculus 0 (F p)).inverse) V ∧
    ContDiff ℝ ∞ (fun p => strongDirichletOperator fixedSobolevCalculus 0 (F1 p)) ∧
    ContDiffOn ℝ ∞ (fun p => nativeWeakHalfLift (coefficientMatrixField 2 (F p)) 0 0 (ha p) sphereFischerInner) V ∧
    ContDiff ℝ ∞ (fun p => weakFirstPoissonVariationL 1 (coefficientMatrixField 2 (F1 p)) (ha1 p)) := by
  let F := commonSupportMatrixFamily 2 A hA S hS hz
  let F1 := commonSupportMatrixFamily 2 A1 hA1 S1 hS1 hz1
  let I := fun p => (strongDirichletOperator fixedSobolevCalculus 0 (F p)).inverse
  let A1op := fun p => strongDirichletOperator fixedSobolevCalculus 0 (F1 p)
  let W := fun p => nativeWeakHalfLift (coefficientMatrixField 2 (F p)) 0 0 (ha p) sphereFischerInner
  let W1 := fun p => weakFirstPoissonVariationL 1 (coefficientMatrixField 2 (F1 p)) (ha1 p)
  have hAS := contDiff_commonSupport_actual_strongDirichletOperator fixedSobolevCalculus 0 A hA S hS hz
  have hA1S : ContDiff ℝ ∞ A1op := contDiff_commonSupport_actual_strongDirichletOperator fixedSobolevCalculus 0 A1 hA1 S1 hS1 hz1
  have hIS : ContDiffOn ℝ ∞ I V := contDiffOn_banachInverseFamily _ V hAS.contDiffOn hStrong
  have hWeakInv (p : P) (hp : p ∈ V) : (commonSupportZeroWeakEnergy A hA p).IsInvertible :=
    nativeZeroCoefficientEnergy_isInvertible (commonSupportEnergyMemLp A hA p) (hCoercive p hp)
  have hWF : W = commonSupportWeakHalfLift A hA := commonSupport_native_weak_lift_family_eq A hA S hS hz ha
  have hWS : ContDiffOn ℝ ∞ W V := hWF ▸ contDiffOn_commonSupportWeakHalfLift A hA S hS hz V hWeakInv
  have hW1F : W1 = fun p => weakFirstPoissonVariationL 1 (fun z => A1 (p,z)) (commonSupportEnergyMemLp A1 hA1 p) :=
    commonSupport_native_weak_first_family_eq A1 hA1 S1 hS1 hz1 ha1
  have hW1S : ContDiff ℝ ∞ W1 := by
    rw [hW1F]
    let J := (TauCeti.w1p0Submodule (volume:Measure X) ballOpens 2).toSubmodule.subtypeL
    let Iw := nativeCoefficientWeakFunctionalInverse (fun _ : X => (1:ℝ) • (1:Mat)) 0 0 (flatCoefficientBound 1)
    change ContDiff ℝ ∞ (fun p => -(J.comp (Iw.comp ((commonSupportWeakEnergy A1 hA1 p).comp fixedHarmonicH1LiftL))))
    exact (contDiff_const.clm_comp (contDiff_const.clm_comp
      ((contDiff_commonSupportWeakEnergy A1 hA1 S1 hS1 hz1).clm_comp contDiff_const))).neg
  exact ⟨hIS,hA1S,hWS,hW1S⟩

end ShrinkingSpheres
