import Proof.HighConormalTaylor
import Proof.ConormalSymmetry

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option maxSynthPendingDepth 15
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set MeasureTheory
open scoped ENNReal
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.EnergyBridge OAI.AnisotropicCalderon.DirichletFamily
open OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open OAI.AnisotropicCalderon.SphereHarmonic OAI.AnisotropicCalderon.SpectralCoreRegularity
open OAI.AnisotropicCalderon.NativeHalfCoefficientConormalTrace

theorem negative_inclusion_halfConormalCoefficient (F : SmoothCoefficientMatrix 2) (U : BallSobolev 2) :
    sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num) (halfConormalCoefficientL F U) =
      sphereSobolevInclusionL 0 (-(1/2:ℝ)) (by norm_num)
        (sphereSobolevZeroEquiv orthogonalSphereHarmonics denseSphereHarmonics
          (ordinaryConormalTraceL fixedSobolevCalculus fixedUnitBallValueTrace F U)) := by
  have hC := congrArg (fun T : BallSobolev 2 →L[ℝ] SphereSobolev (1/2:ℝ) =>
    sphereSobolevInclusionL (1/2:ℝ) 0 (by norm_num) (T U)) (halfConormalCoefficientL_eq_native F)
  have hN := sphereSobolevInclusionL_nativeHalfCoefficientConormalTraceL sphereFischerInner
    orthogonalSphereHarmonics denseSphereHarmonics fixedSobolevCalculus fixedUnitBallValueTrace F U
  have hTrans := congrArg (fun T : SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ)) =>
    T (halfConormalCoefficientL F U))
      (sphereSobolevInclusionL_trans (1/2:ℝ) 0 (-(1/2:ℝ)) (by norm_num) (by norm_num))
  exact hTrans.symm.trans (congrArg (sphereSobolevInclusionL 0 (-(1/2:ℝ)) (by norm_num)) (hC.trans hN))

theorem actual_conormal_endpoints_compatible {a : X → Mat}
    (ha : MemLp (fun x => TauCeti.PDE.energyIntegrand (a x) 0 0) ⊤ ((volume:Measure X).restrict ballOpens))
    (hc : IsCoercive (TauCeti.PDE.energyFormH1L0 ha))
    (F : SmoothCoefficientMatrix 2)
    (hPoint : ∀ x ∈ (ballOpens:Set X),coefficientMatrixField 2 F x = a x)
    (hInv : (strongDirichletOperator fixedSobolevCalculus 0 F).IsInvertible) :
    (sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)).comp (actualHighConormalL F) =
      (nativeWeakConormalEndpoint a 0 0 ha sphereFischerInner).comp
        (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)) := by
  apply ContinuousLinearMap.ext
  intro f
  let U := strongPoissonL F f
  let g := sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num) f
  have hLift := nativeWeakHalfLift_eq_strongPoisson ha hc F hPoint hInv f
  have hHarm := fullCoefficientOperator_strongPoissonL F hInv f
  have hN := nativeWeakConormal_eq_ordinary_trace ha F hPoint g U hLift hHarm
  exact (negative_inclusion_halfConormalCoefficient F U).trans hN.symm

theorem flat_conormal_endpoints_compatible (c : ℝ) :
    (sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)).comp (highConormalFlatL c) =
      (c • fixedLowRadialL).comp (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)) := by
  apply ContinuousLinearMap.ext
  intro f
  have hEq := (negative_inclusion_halfOutwardTrace (fixedHarmonicLiftL f)).trans (fixedLowRadialL_high f).symm
  exact ((sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)).map_smul c
    (fixedHalfOutwardTraceL (fixedHarmonicLiftL f))).trans
      (congrArg (fun z : SphereSobolev (-(1/2:ℝ)) => c • z) hEq)

theorem first_conormal_endpoints_compatible (F0 F1 : SmoothCoefficientMatrix 2) (c : ℝ) (hc : 0 < c)
    (hF0 : ∀ x ∈ (ballOpens:Set X),coefficientMatrixField 2 F0 x = 1)
    (ha1 : MemLp (fun x => TauCeti.PDE.energyIntegrand (coefficientMatrixField 2 F1 x) 0 0) ⊤
      ((volume:Measure X).restrict ballOpens))
    (hInv0 : (strongDirichletOperator fixedSobolevCalculus 0 (c • F0)).IsInvertible) :
    (sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)).comp
      (highFirstConormalVariationL F0 F1 c) =
      (weakFirstConormalVariationL c (coefficientMatrixField 2 F1) ha1).comp
        (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)) := by
  apply ContinuousLinearMap.ext
  intro f
  let U1 := strongFirstPoissonVariationL F0 F1 c f
  let U0 := fixedHarmonicLiftL f
  let I0 := sphereSobolevInclusionL 0 (-(1/2:ℝ)) (by norm_num)
  let IH := sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)
  let Z := sphereSobolevZeroEquiv orthogonalSphereHarmonics denseSphereHarmonics
  let C0 := ordinaryConormalTraceL fixedSobolevCalculus fixedUnitBallValueTrace (c • F0) U1
  let C1 := ordinaryConormalTraceL fixedSobolevCalculus fixedUnitBallValueTrace F1 U0
  have h0 := negative_inclusion_halfConormalCoefficient (c • F0) U1
  have h1 := negative_inclusion_halfConormalCoefficient F1 U0
  have hN := weakFirstConormal_high_flux F0 F1 c hc hF0 ha1 hInv0 f
  have hMerge : I0 (Z (C0+C1)) = I0 (Z C0)+I0 (Z C1) :=
    (congrArg I0 (Z.map_add C0 C1)).trans (I0.map_add _ _)
  have hSum := congrArg₂ (fun u v : SphereSobolev (-(1/2:ℝ)) => u+v) h0 h1
  exact (IH.map_add (halfConormalCoefficientL (c • F0) U1) (halfConormalCoefficientL F1 U0)).trans
    (hSum.trans (hMerge.symm.trans hN.symm))

theorem conormalTaylor_endpoints_compatible {a : X → Mat}
    (ha : MemLp (fun x => TauCeti.PDE.energyIntegrand (a x) 0 0) ⊤ ((volume:Measure X).restrict ballOpens))
    (hCoerce : IsCoercive (TauCeti.PDE.energyFormH1L0 ha))
    (F F0 F1 : SmoothCoefficientMatrix 2) (c r : ℝ) (hc : 0 < c)
    (hPoint : ∀ x ∈ (ballOpens:Set X),coefficientMatrixField 2 F x = a x)
    (hF0 : ∀ x ∈ (ballOpens:Set X),coefficientMatrixField 2 F0 x = 1)
    (ha1 : MemLp (fun x => TauCeti.PDE.energyIntegrand (coefficientMatrixField 2 F1 x) 0 0) ⊤
      ((volume:Measure X).restrict ballOpens))
    (hInv : (strongDirichletOperator fixedSobolevCalculus 0 F).IsInvertible)
    (hInv0 : (strongDirichletOperator fixedSobolevCalculus 0 (c • F0)).IsInvertible) :
    (sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)).comp
      (actualHighConormalL F-highConormalFlatL c-r • highFirstConormalVariationL F0 F1 c) =
      (nativeWeakConormalEndpoint a 0 0 ha sphereFischerInner-c • fixedLowRadialL-
        r • weakFirstConormalVariationL c (coefficientMatrixField 2 F1) ha1).comp
          (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)) := by
  have h0 := actual_conormal_endpoints_compatible ha hCoerce F hPoint hInv
  have h1 := flat_conormal_endpoints_compatible c
  have h2 := first_conormal_endpoints_compatible F0 F1 c hc hF0 ha1 hInv0
  have h01 := congrArg₂ (fun A B : SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ)) => A-B) h0 h1
  have hAll := congrArg₂ (fun A B : SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ)) => A-r • B) h01 h2
  simpa only [ContinuousLinearMap.comp_sub,ContinuousLinearMap.comp_smul,
    ContinuousLinearMap.sub_comp,ContinuousLinearMap.smul_comp] using hAll

end ShrinkingSpheres
