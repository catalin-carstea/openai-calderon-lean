import Proof.SharpBoundaryCoefficientMultiplier
import Proof.FlatFullCoefficientOperator

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option maxSynthPendingDepth 15
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set
open scoped ENNReal
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.EnergyBridge OAI.AnisotropicCalderon.DirichletFamily
open OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open OAI.AnisotropicCalderon.SphereHarmonic OAI.AnisotropicCalderon.SpectralCoreRegularity
open OAI.AnisotropicCalderon.NativeCoefficientBoundaryMultiplier
open OAI.AnisotropicCalderon.NativeHalfSmoothMultiplier

abbrev halfBoundaryCoefficientMulL (F : SmoothCoefficientJets 2) :=
  nativeHalfCoefficientMulL fixedSobolevCalculus sphereFischerInner orthogonalSphereHarmonics
    denseSphereHarmonics fixedUnitBallValueTrace F

abbrev negativeBoundaryCoefficientMulL (F : SmoothCoefficientJets 2) :=
  nativeNegativeHalfCoefficientMulL fixedSobolevCalculus sphereFischerInner orthogonalSphereHarmonics
    denseSphereHarmonics fixedUnitBallValueTrace F

lemma halfBoundaryCoefficientMulL_add (F G : SmoothCoefficientJets 2) :
    halfBoundaryCoefficientMulL (F+G) = halfBoundaryCoefficientMulL F+halfBoundaryCoefficientMulL G := by
  apply ContinuousLinearMap.ext
  intro f
  simp only [halfBoundaryCoefficientMulL,nativeHalfCoefficientMulL,ContinuousLinearMap.comp_apply,_root_.add_apply]
  rw [coefficientMultiplier_add fixedSobolevCalculus 1 F G]
  simp only [_root_.add_apply,map_add]

lemma halfBoundaryCoefficientMulL_smul (c : ℝ) (F : SmoothCoefficientJets 2) :
    halfBoundaryCoefficientMulL (c • F) = c • halfBoundaryCoefficientMulL F := by
  apply ContinuousLinearMap.ext
  intro f
  simp only [halfBoundaryCoefficientMulL,nativeHalfCoefficientMulL,ContinuousLinearMap.comp_apply,_root_.smul_apply]
  rw [coefficientMultiplier_smul fixedSobolevCalculus 1 c F]
  simp only [_root_.smul_apply,map_smul]

lemma negativeBoundaryCoefficientMulL_add (F G : SmoothCoefficientJets 2) :
    negativeBoundaryCoefficientMulL (F+G) = negativeBoundaryCoefficientMulL F+negativeBoundaryCoefficientMulL G := by
  change realHalfOperatorAdjointL (halfBoundaryCoefficientMulL (F+G)) =
    realHalfOperatorAdjointL (halfBoundaryCoefficientMulL F)+realHalfOperatorAdjointL (halfBoundaryCoefficientMulL G)
  exact (congrArg (fun A => realHalfOperatorAdjointL A) (halfBoundaryCoefficientMulL_add F G)).trans
    (realHalfOperatorAdjointL.map_add _ _)

lemma negativeBoundaryCoefficientMulL_smul (c : ℝ) (F : SmoothCoefficientJets 2) :
    negativeBoundaryCoefficientMulL (c • F) = c • negativeBoundaryCoefficientMulL F := by
  change realHalfOperatorAdjointL (halfBoundaryCoefficientMulL (c • F)) =
    c • realHalfOperatorAdjointL (halfBoundaryCoefficientMulL F)
  exact (congrArg (fun A => realHalfOperatorAdjointL A) (halfBoundaryCoefficientMulL_smul c F)).trans
    (realHalfOperatorAdjointL.map_smul c _)

lemma halfBoundaryCoefficientMulL_one (F : SmoothCoefficientJets 2)
    (hF : ∀ x ∈ (ballOpens : Set X),coefficientValue 2 F x = 1) :
    halfBoundaryCoefficientMulL F = ContinuousLinearMap.id ℝ (SphereSobolev (1/2:ℝ)) := by
  apply ContinuousLinearMap.ext
  intro f
  change fixedHalfValueTraceL (TauCeti.Wkp.firstOrder 0
    (coefficientMultiplier fixedSobolevCalculus 1 F (fixedHarmonicH1LiftL f))) = f
  rw [coefficientMultiplier_eq_const_of_on_ball fixedSobolevCalculus 1 F 1 hF,one_smul,ContinuousLinearMap.id_apply,
    TauCeti.Wkp.firstOrder_zero]
  exact congrArg (fun T : SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ) => T f)
    fixedHalfValueTrace_right_inverse

lemma negativeBoundaryCoefficientMulL_one (F : SmoothCoefficientJets 2)
    (hF : ∀ x ∈ (ballOpens : Set X),coefficientValue 2 F x = 1) :
    negativeBoundaryCoefficientMulL F = ContinuousLinearMap.id ℝ (SphereSobolev (-(1/2:ℝ))) := by
  change ContinuousLinearMap.adjoint (halfBoundaryCoefficientMulL F) = ContinuousLinearMap.id ℝ _
  rw [halfBoundaryCoefficientMulL_one F hF]
  simp

/-- Boundary coefficient operators depend only on their literal sphere values. -/
theorem halfBoundaryCoefficientMulL_congr_sphere (F G : SmoothCoefficientJets 2)
    (hSphere : ∀ w : UnitSphere,coefficientValue 2 F w.val = coefficientValue 2 G w.val) :
    halfBoundaryCoefficientMulL F = halfBoundaryCoefficientMulL G := by
  obtain ⟨M,hM,hm,hgm⟩ := exists_smooth_ball_multiplier_bound (coefficientSmoothData F)
  obtain ⟨N,hN,hn,hgn⟩ := exists_smooth_ball_multiplier_bound (coefficientSmoothData G)
  have hS : smoothSphereValue (coefficientSmoothData F) = smoothSphereValue (coefficientSmoothData G) :=
    ContinuousMap.ext hSphere
  exact (nativeHalfCoefficientMulL_eq_smoothMulL fixedSobolevCalculus sphereFischerInner orthogonalSphereHarmonics
    denseSphereHarmonics fixedUnitBallValueTrace F hM hm hgm).trans
    ((nativeHalfSmoothMulL_eq_of_sphereValue_eq sphereFischerInner orthogonalSphereHarmonics denseSphereHarmonics
      fixedUnitBallValueTrace (coefficientSmoothData F) (coefficientSmoothData G) hM hN hm hgm hn hgn hS).trans
      (nativeHalfCoefficientMulL_eq_smoothMulL fixedSobolevCalculus sphereFischerInner orthogonalSphereHarmonics
        denseSphereHarmonics fixedUnitBallValueTrace G hN hn hgn).symm)

theorem negativeBoundaryCoefficientMulL_congr_sphere (F G : SmoothCoefficientJets 2)
    (hSphere : ∀ w : UnitSphere,coefficientValue 2 F w.val = coefficientValue 2 G w.val) :
    negativeBoundaryCoefficientMulL F = negativeBoundaryCoefficientMulL G := by
  change ContinuousLinearMap.adjoint (halfBoundaryCoefficientMulL F) =
    ContinuousLinearMap.adjoint (halfBoundaryCoefficientMulL G)
  exact congrArg (fun A : SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ) => ContinuousLinearMap.adjoint A)
    (halfBoundaryCoefficientMulL_congr_sphere F G hSphere)

end ShrinkingSpheres
