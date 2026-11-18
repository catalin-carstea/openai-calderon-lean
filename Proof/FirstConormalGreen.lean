import Proof.FirstVariationGreen
import Proof.WeakConormalTaylor
import Proof.WeakStrongFirstVariation
import Proof.WeakConormalStrongTrace

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1700000
set_option maxSynthPendingDepth 15
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set MeasureTheory
open scoped ENNReal InnerProductSpace
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.EnergyBridge OAI.AnisotropicCalderon.DirichletFamily
open OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open OAI.AnisotropicCalderon.SphereHarmonic OAI.AnisotropicCalderon.SpectralCoreRegularity
open OAI.AnisotropicCalderon.NativePolynomialBulkMoments OAI.AnisotropicCalderon.NativeFullSharpHalfTrace
open OAI.AnisotropicCalderon.NativeHalfCoefficientConormalTrace OAI.AnisotropicCalderon.NativeHalfTraceRightInverse
open OAI.AnisotropicCalderon.NativeSmoothSharpTraceCompletion
open OAI.AnisotropicCalderon.NativeHarmonicLiftOrderCoherence

lemma weakFirstConormal_dualPairing (c : ℝ) {a1 : X → Mat}
    (ha1 : MemLp (fun x => TauCeti.PDE.energyIntegrand (a1 x) 0 0) ⊤ ((volume:Measure X).restrict ballOpens))
    (f z : SphereSobolev (1/2:ℝ)) :
    sphereSobolevDualPairing (1/2:ℝ) z (weakFirstConormalVariationL c a1 ha1 f) =
      sphereSurfaceMass⁻¹*(TauCeti.PDE.energyFormH1 (fun _ : X => c • (1:Mat)) 0 0
        (weakFirstPoissonVariationL c a1 ha1 f) (fixedHarmonicH1LiftL z)+
      TauCeti.PDE.energyFormH1 a1 0 0 (fixedHarmonicH1LiftL f) (fixedHarmonicH1LiftL z)) := by
  unfold weakFirstConormalVariationL
  rw [ContinuousLinearMap.comp_apply,sphereSobolevDualPairing_dualRiesz]
  simp only [_root_.smul_apply,_root_.add_apply,ContinuousLinearMap.bilinearComp_apply,smul_eq_mul]
  rw [TauCeti.PDE.energyFormH1L_apply,TauCeti.PDE.energyFormH1L_apply]
  rfl

/-- The weak first conormal variation is the sum of the actual strong first
    solution flux and the actual first coefficient flux. -/
theorem weakFirstConormal_high_flux (F0 F1 : SmoothCoefficientMatrix 2) (c : ℝ) (hc : 0 < c)
    (hF0 : ∀ x ∈ (ballOpens:Set X),coefficientMatrixField 2 F0 x = 1)
    (ha1 : MemLp (fun x => TauCeti.PDE.energyIntegrand (coefficientMatrixField 2 F1 x) 0 0) ⊤
      ((volume:Measure X).restrict ballOpens))
    (hInv0 : (strongDirichletOperator fixedSobolevCalculus 0 (c • F0)).IsInvertible)
    (f : SphereSobolev (3/2:ℝ)) :
    weakFirstConormalVariationL c (coefficientMatrixField 2 F1) ha1
      (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num) f) =
      sphereSobolevInclusionL 0 (-(1/2:ℝ)) (by norm_num)
        (sphereSobolevZeroEquiv orthogonalSphereHarmonics denseSphereHarmonics
          (ordinaryConormalTraceL fixedSobolevCalculus fixedUnitBallValueTrace (c • F0)
            (strongFirstPoissonVariationL F0 F1 c f)+
           ordinaryConormalTraceL fixedSobolevCalculus fixedUnitBallValueTrace F1 (fixedHarmonicLiftL f))) := by
  let U0 := fixedHarmonicLiftL f
  let U1 := strongFirstPoissonVariationL F0 F1 c f
  let g := sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num) f
  have hOrder : TauCeti.Wkp.firstOrder 1 U0 = fixedHarmonicH1LiftL g :=
    firstOrder_harmonicLiftCompletion sphereFischerInner orthogonalSphereHarmonics f
  have hP1 := weakFirstPoissonVariation_high_compatible F0 F1 c hc hF0 ha1 hInv0 f
  have hPoint (x : X) (hx : x ∈ (ballOpens:Set X)) : coefficientMatrixField 2 (c • F0) x = c • (1:Mat) := by
    rw [coefficientMatrixField_smul,hF0 x hx]
  have hForce : fullCoefficientOperatorL fixedSobolevCalculus 0 (c • F0) U1+
      fullCoefficientOperatorL fixedSobolevCalculus 0 F1 U0 = 0 := by
    let W := (strongDirichletOperator fixedSobolevCalculus 0 (c • F0)).inverse
      (fullCoefficientOperatorL fixedSobolevCalculus 0 F1 U0)
    have hRestr := congrArg (fun T => T W) (fullCoefficientOperatorL_comp_subtype fixedSobolevCalculus 0 (c • F0))
    have hSolve : fullCoefficientOperatorL fixedSobolevCalculus 0 (c • F0) (W:BallSobolev 2) =
        fullCoefficientOperatorL fixedSobolevCalculus 0 F1 U0 := hRestr.trans (hInv0.self_apply_inverse _)
    change fullCoefficientOperatorL fixedSobolevCalculus 0 (c • F0) (-(W:BallSobolev 2))+_ = 0
    rw [map_neg,hSolve,neg_add_cancel]
  apply ext_inner_left ℝ
  intro z
  change sphereSobolevDualPairing (1/2:ℝ) z _ = sphereSobolevDualPairing (1/2:ℝ) z _
  rw [weakFirstConormal_dualPairing,hP1,← hOrder]
  have hEnergy := firstVariation_full_test_energy_Green (c • F0) F1 U0 U1 hForce (fixedHarmonicH1LiftL z)
  have hE0Eq : TauCeti.PDE.energyFormH1 (coefficientMatrixField 2 (c • F0)) 0 0
      (TauCeti.Wkp.firstOrder 1 U1) (fixedHarmonicH1LiftL z) =
      TauCeti.PDE.energyFormH1 (fun _ : X => c • (1:Mat)) 0 0
        (TauCeti.Wkp.firstOrder 1 U1) (fixedHarmonicH1LiftL z) :=
    energyFormH1_congr_coeff_on hPoint (TauCeti.Wkp.firstOrder 1 U1) (fixedHarmonicH1LiftL z)
  rw [hE0Eq] at hEnergy
  rw [hEnergy,← mul_assoc,inv_mul_cancel₀ sphereSurfaceMass_pos.ne',one_mul]
  apply Eq.symm
  apply boundary_negative_pairing z
    (nativeHalfCoefficientConormalTraceL sphereFischerInner orthogonalSphereHarmonics denseSphereHarmonics
      fixedSobolevCalculus fixedUnitBallValueTrace (c • F0) U1+
     nativeHalfCoefficientConormalTraceL sphereFischerInner orthogonalSphereHarmonics denseSphereHarmonics
      fixedSobolevCalculus fixedUnitBallValueTrace F1 U0)
  · rw [map_add,sphereSobolevInclusionL_nativeHalfCoefficientConormalTraceL,
      sphereSobolevInclusionL_nativeHalfCoefficientConormalTraceL,map_add]
  · have ht := sphereSobolevInclusionL_nativeHalfTraceL sphereFischerInner orthogonalSphereHarmonics
      denseSphereHarmonics fixedUnitBallValueTrace (fixedHarmonicH1LiftL z)
    have hr := nativeHalfTraceL_harmonicFirstOrderLiftCompletion sphereFischerInner
      orthogonalSphereHarmonics denseSphereHarmonics fixedUnitBallValueTrace z
    exact (congrArg (sphereSobolevInclusionL (1/2:ℝ) 0 (by norm_num)) hr).symm.trans ht

end ShrinkingSpheres
