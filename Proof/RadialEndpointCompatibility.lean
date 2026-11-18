import Proof.ActualLowRadialEndpoint

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxSynthPendingDepth 15
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set MeasureTheory
open scoped ENNReal
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.EnergyBridge OAI.AnisotropicCalderon.DirichletFamily
open OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open OAI.AnisotropicCalderon.SphereHarmonic OAI.AnisotropicCalderon.SpectralCoreRegularity

abbrev actualHighRadialErrorL (F : SmoothCoefficientMatrix 2) :
    SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ) :=
  fixedHalfOutwardTraceL.comp (strongPoissonL F)-fixedHalfOutwardTraceL.comp fixedHarmonicLiftL

lemma negative_inclusion_halfOutwardTrace (U : BallSobolev 2) :
    sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num) (fixedHalfOutwardTraceL U) =
      sphereSobolevInclusionL 0 (-(1/2:ℝ)) (by norm_num)
        (sphereSobolevZeroEquiv orthogonalSphereHarmonics denseSphereHarmonics
          (outwardRadialTraceL fixedSobolevCalculus fixedUnitBallValueTrace U)) := by
  have hTrans := congrArg (fun T : SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ)) =>
      T (fixedHalfOutwardTraceL U))
    (sphereSobolevInclusionL_trans (1/2:ℝ) 0 (-(1/2:ℝ)) (by norm_num) (by norm_num))
  have hZero := OAI.AnisotropicCalderon.NativeFullHalfRadialTrace.sphereSobolevInclusionL_nativeHalfOutwardTraceL
    sphereFischerInner orthogonalSphereHarmonics denseSphereHarmonics fixedSobolevCalculus fixedUnitBallValueTrace U
  simp only [ContinuousLinearMap.comp_apply] at hTrans
  exact hTrans.symm.trans (congrArg (sphereSobolevInclusionL 0 (-(1/2:ℝ)) (by norm_num)) hZero)

/-- The actual low radial endpoint and high radial endpoint are compatible.
    This is the mathematical identity required by midpoint interpolation. -/
theorem actual_radial_endpoints_compatible {a : X → Mat}
    (hcoeff : MemLp (fun x => TauCeti.PDE.energyIntegrand (a x) 0 0)
      ⊤ ((volume:Measure X).restrict ballOpens))
    (hc : IsCoercive (TauCeti.PDE.energyFormH1L0 (mu:=(volume:Measure X))
      (Omega:=ballOpens) (a:=a) (b:=fun _ => (0:X)) (c:=fun _ => (0:ℝ)) hcoeff))
    (F : SmoothCoefficientMatrix 2)
    (hPoint : ∀ x ∈ (ballOpens : Set X),coefficientMatrixField 2 F x = a x)
    (hInv : (strongDirichletOperator fixedSobolevCalculus 0 F).IsInvertible)
    (hNormalInv : (negativeBoundaryCoefficientMulL (normalCoefficientJet F)).IsInvertible) :
    (sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)).comp (actualHighRadialErrorL F) =
      (actualLowRadialErrorL a hcoeff F).comp
        (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)) := by
  apply ContinuousLinearMap.ext
  intro f
  let g := sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num) f
  let U := strongPoissonL F f
  let M := negativeBoundaryCoefficientMulL (normalCoefficientJet F)
  let R := sphereSobolevInclusionL 0 (-(1/2:ℝ)) (by norm_num)
    (sphereSobolevZeroEquiv orthogonalSphereHarmonics denseSphereHarmonics
      (outwardRadialTraceL fixedSobolevCalculus fixedUnitBallValueTrace U))
  let A := nativeWeakConormalEndpoint a (fun _ => (0:X)) (fun _ => (0:ℝ)) hcoeff sphereFischerInner
  let T (j : I) := negativeBoundaryCoefficientMulL (tangentCoefficientJet F j)
  let S := ∑ j : I,T j (fixedSphereTangentialL j g)
  have hHarm : ordinaryPrincipalL fixedSobolevCalculus 0 F U = 0 :=
    fullCoefficientOperator_strongPoissonL F hInv f
  have hLift := nativeWeakHalfLift_eq_strongPoisson hcoeff hc F hPoint hInv f
  have hConormal := nativeWeakConormal_eq_ordinary_trace hcoeff F hPoint g U hLift hHarm
  have hConversion := nativeH2_conormal_negativeHalf_eq_coefficient_normal_add_tangent
    fixedSobolevCalculus sphereFischerInner orthogonalSphereHarmonics denseSphereHarmonics
      fixedUnitBallValueTrace F (normalCoefficientJet F) (tangentCoefficientJet F)
      (coefficientSmoothData_normalCoefficientJet F) (coefficientSmoothData_tangentCoefficientJet F) U
  have hValue := fixedHalfValueTrace_strongPoisson F f
  change OAI.AnisotropicCalderon.NativeFullSharpHalfTrace.nativeHalfTraceL
    sphereFischerInner orthogonalSphereHarmonics denseSphereHarmonics fixedUnitBallValueTrace
      (TauCeti.Wkp.firstOrder 1 U) = g at hValue
  rw [hValue] at hConversion
  have hA : A g = M R+S := hConormal.trans hConversion
  have hInside : A g-M (fixedLowRadialL g)-S = M (R-fixedLowRadialL g) := by
    rw [hA,M.map_sub]
    abel
  have hLow : actualLowRadialErrorL a hcoeff F g = R-fixedLowRadialL g := by
    change M.inverse (A g-M (fixedLowRadialL g)-S) = _
    rw [hInside]
    exact hNormalInv.inverse_apply_self _
  change sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)
    (fixedHalfOutwardTraceL U-fixedHalfOutwardTraceL (fixedHarmonicLiftL f)) = _
  rw [map_sub,negative_inclusion_halfOutwardTrace,negative_inclusion_halfOutwardTrace]
  exact ((congrArg (fun z => R-z) (fixedLowRadialL_high f)).symm).trans hLow.symm

end ShrinkingSpheres
