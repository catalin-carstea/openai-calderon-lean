import Proof.CommonSupportWeakEnergyRegularity

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option maxSynthPendingDepth 20
set_option synthInstance.maxHeartbeats 100000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter MeasureTheory
open scoped ContDiff Topology ENNReal Matrix.Norms.Elementwise
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.EnergyBridge OAI.AnisotropicCalderon.DirichletFamily
open OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open OAI.AnisotropicCalderon.SphereHarmonic OAI.AnisotropicCalderon.NativeHarmonicH1LiftCompletion
open OAI.AnisotropicCalderon.NativePolynomialBulkMoments
attribute [local instance] TauCeti.W1p0.instNormedAddCommGroup TauCeti.W1p0.instInnerProductSpace
variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]

lemma nativeZeroFunctionalInverse_eq_map_inverse
    (B : BallH1Zero →L[ℝ] StrongDual ℝ BallH1Zero) : nativeZeroFunctionalInverse B = B.inverse := by
  change functionalInverse B = B.inverse
  exact functionalInverse_eq_inverse B

def commonSupportWeakHalfLift (a : P × X → Mat) (ha : ContDiff ℝ ∞ a) (p : P) :
    SphereSobolev (1/2:ℝ) →L[ℝ] BallH1 :=
  nativeWeakHalfLift (fun z => a (p,z)) (fun _ => (0:X)) (fun _ => (0:ℝ))
    (commonSupportEnergyMemLp a ha p) sphereFischerInner

def commonSupportWeakConormalEndpoint (a : P × X → Mat) (ha : ContDiff ℝ ∞ a) (p : P) :
    SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ)) :=
  nativeWeakConormalEndpoint (fun z => a (p,z)) (fun _ => (0:X)) (fun _ => (0:ℝ))
    (commonSupportEnergyMemLp a ha p) sphereFischerInner

/-- The actual native half-order Poisson lift is smooth on its genuine weak
    inverse locus. Proof-valued coefficient witnesses are shared throughout. -/
theorem contDiffOn_commonSupportWeakHalfLift
    (a : P × X → Mat) (ha : ContDiff ℝ ∞ a) (S : Set X) (hS : IsCompact S)
    (hz : ∀ p z,z ∉ S → a (p,z) = 0) (V : Set P)
    (hInv : ∀ p ∈ V,(commonSupportZeroWeakEnergy a ha p).IsInvertible) :
    ContDiffOn ℝ ∞ (commonSupportWeakHalfLift a ha) V := by
  have hEnergy := contDiff_commonSupportWeakEnergy a ha S hS hz
  have hZero := contDiff_commonSupportZeroWeakEnergy a ha S hS hz
  have hInverse := contDiffOn_banachInverseFamily _ V hZero.contDiffOn hInv
  let J := (TauCeti.w1p0Submodule (volume : Measure X) ballOpens 2).toSubmodule.subtypeL
  let H := harmonicFirstOrderLiftCompletion sphereFischerInner
  have hEq : commonSupportWeakHalfLift a ha = (fun p =>
      ((ContinuousLinearMap.id ℝ BallH1)-J.comp
        ((nativeZeroFunctionalInverse (commonSupportZeroWeakEnergy a ha p)).comp
          (commonSupportWeakEnergy a ha p))).comp H) := by
    funext p
    rfl
  simp only [nativeZeroFunctionalInverse_eq_map_inverse] at hEq
  rw [hEq]
  have hCorrection : ContDiffOn ℝ ∞ (fun p => J.comp
      ((commonSupportZeroWeakEnergy a ha p).inverse.comp (commonSupportWeakEnergy a ha p))) V :=
    contDiffOn_const.clm_comp (hInverse.clm_comp hEnergy.contDiffOn)
  exact (contDiffOn_const.sub hCorrection).clm_comp contDiffOn_const

/-- The genuine weak conormal response is smooth as a half-order Sobolev
    operator, via the actual energy form and actual weak harmonic lift. -/
theorem contDiffOn_commonSupportWeakConormalEndpoint
    (a : P × X → Mat) (ha : ContDiff ℝ ∞ a) (S : Set X) (hS : IsCompact S)
    (hz : ∀ p z,z ∉ S → a (p,z) = 0) (V : Set P)
    (hInv : ∀ p ∈ V,(commonSupportZeroWeakEnergy a ha p).IsInvertible) :
    ContDiffOn ℝ ∞ (commonSupportWeakConormalEndpoint a ha) V := by
  let H := harmonicFirstOrderLiftCompletion sphereFischerInner
  let Post : StrongDual ℝ BallH1 →L[ℝ] StrongDual ℝ (SphereSobolev (1/2:ℝ)) :=
    (ContinuousLinearMap.compL ℝ (SphereSobolev (1/2:ℝ)) BallH1 ℝ).flip H
  have hEq : commonSupportWeakConormalEndpoint a ha = (fun p =>
      (sphereSobolevDualRieszL (1/2:ℝ)).comp (sphereSurfaceMass⁻¹ •
        Post.comp ((commonSupportFullWeakEnergy a ha p).comp (commonSupportWeakHalfLift a ha p)))) := by
    funext p
    rfl
  rw [hEq]
  have hEnergy := contDiff_commonSupportFullWeakEnergy a ha S hS hz
  have hLift := contDiffOn_commonSupportWeakHalfLift a ha S hS hz V hInv
  have hPair : ContDiffOn ℝ ∞ (fun p => Post.comp
      ((commonSupportFullWeakEnergy a ha p).comp (commonSupportWeakHalfLift a ha p))) V :=
    contDiffOn_const.clm_comp (hEnergy.contDiffOn.clm_comp hLift)
  exact contDiffOn_const.clm_comp (hPair.const_smul sphereSurfaceMass⁻¹)

end ShrinkingSpheres
