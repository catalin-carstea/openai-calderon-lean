import Proof.StrongFirstMultiplierDefect
import Proof.FirstRadialOrderZero

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter MeasureTheory
open scoped ContDiff Topology ENNReal
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.EnergyBridge OAI.AnisotropicCalderon.DirichletFamily
open OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open OAI.AnisotropicCalderon.SphereHarmonic OAI.AnisotropicCalderon.SpectralCoreRegularity
open OAI.AnisotropicCalderon.NativeThreeHalfCoefficientMultiplier
open OAI.AnisotropicCalderon.NativeCoefficientBoundaryMultiplier
open OAI.AnisotropicCalderon.NativeOrderOneCoefficientMultiplier
open OAI.AnisotropicCalderon.NativeFullSharpHalfTrace
attribute [local instance] TauCeti.W1p0.instNormedAddCommGroup TauCeti.W1p0.instInnerProductSpace
attribute [local irreducible] nativeCoefficientWeakEnergyL nativeCoefficientWeakFunctionalInverse functionalInverse nativeZeroFunctionalInverse

/-- The actual first strong Poisson variation has the same linearized
multiplication defect, on the whole high boundary domain. -/
theorem strongFirstPoisson_smooth_multiplier_difference (F0 F1 : SmoothCoefficientMatrix 2)
    (ha0 : MemLp (fun z => TauCeti.PDE.energyIntegrand (coefficientMatrixField 2 F0 z) 0 0) ⊤
      ((volume:Measure X).restrict ballOpens))
    (ha1 : MemLp (fun z => TauCeti.PDE.energyIntegrand (coefficientMatrixField 2 F1 z) 0 0) ⊤
      ((volume:Measure X).restrict ballOpens))
    (hc0 : IsCoercive (TauCeti.PDE.energyFormH1L0 ha0))
    (hFlat : ∀ z ∈ (ballOpens:Set X),coefficientMatrixField 2 F0 z = 1)
    (hInv0 : (strongDirichletOperator fixedSobolevCalculus 0 F0).IsInvertible)
    (Q : SmoothCoefficientJets 3) (f : SphereSobolev (3/2:ℝ)) :
    strongFirstPoissonVariationL F0 F1 1 (nativeThreeHalfCoefficientMulL fixedSobolevCalculus sphereFischerInner
      orthogonalSphereHarmonics denseSphereHarmonics fixedUnitBallValueTrace Q f)-
      coefficientMultiplier fixedSobolevCalculus 2 Q (strongFirstPoissonVariationL F0 F1 1 f) =
    strongFirstMultiplierDefectL F0 F1 ha1 Q (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num) f) := by
  let P := strongFirstPoissonVariationL F0 F1 1
  let W := weakFirstPoissonVariationL 1 (coefficientMatrixField 2 F1) ha1
  let V := strongFirstMultiplierDefectL F0 F1 ha1 Q
  let I0 := sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)
  let J : BallSobolev 2 →L[ℝ] BallH1 := TauCeti.Wkp.firstOrderL 1
  let S := nativeCoefficientH1ProductL fixedSobolevCalculus (smoothMultiplierLowerJets Q)
  let M3 := nativeThreeHalfCoefficientMulL fixedSobolevCalculus sphereFischerInner orthogonalSphereHarmonics denseSphereHarmonics fixedUnitBallValueTrace Q
  let M1 := nativeHalfCoefficientMulL fixedSobolevCalculus sphereFischerInner orthogonalSphereHarmonics denseSphereHarmonics fixedUnitBallValueTrace (smoothMultiplierLowerJets Q)
  have hP (v : SphereSobolev (3/2:ℝ)) : J (P v) = W (I0 v) := by
    exact (weakFirstPoissonVariation_high_compatible F0 F1 1 (by norm_num) hFlat ha1
      (by simpa only [one_smul] using hInv0) v).symm
  have hV : J (V (I0 f)) = W (M1 (I0 f))-S (W (I0 f)) :=
    firstOrder_strongFirstMultiplierDefect F0 F1 ha0 ha1 hc0 hFlat hInv0 Q (I0 f)
  have hX : J (coefficientMultiplier fixedSobolevCalculus 2 Q (P f)) = S (J (P f)) :=
    firstOrder_H2SmoothMultiplier_eq_H1Product fixedSobolevCalculus Q (P f)
  have hI : I0 (M3 f) = M1 (I0 f) :=
    congrArg (fun A : SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ) => A f)
      (nativeCoefficientMulL_high_half_compatibility fixedSobolevCalculus sphereFischerInner orthogonalSphereHarmonics
        denseSphereHarmonics fixedUnitBallValueTrace Q (smoothMultiplierLowerJets Q) (coefficientValue_smoothMultiplierLowerJets Q).symm)
  have h1 : J (P (M3 f)) = W (M1 (I0 f)) := (hP (M3 f)).trans (congrArg W hI)
  have h2 : J (coefficientMultiplier fixedSobolevCalculus 2 Q (P f)) = S (W (I0 f)) := hX.trans (congrArg S (hP f))
  apply nativeH2_firstOrder_injective
  change J (P (M3 f)-coefficientMultiplier fixedSobolevCalculus 2 Q (P f)) = J (V (I0 f))
  exact (J.map_sub _ _).trans ((congrArg₂ (fun x y : BallH1 => x-y) h1 h2).trans hV.symm)

/-- The gained first boundary variation is EXACTLY the commutator of the
actual high radial first correction; its normal-derivative multiplier term
vanishes because the first Poisson variation has zero boundary data. -/
theorem halfMultiplierFirstVariation_high (F0 F1 : SmoothCoefficientMatrix 2)
    (ha0 : MemLp (fun z => TauCeti.PDE.energyIntegrand (coefficientMatrixField 2 F0 z) 0 0) ⊤
      ((volume:Measure X).restrict ballOpens))
    (ha1 : MemLp (fun z => TauCeti.PDE.energyIntegrand (coefficientMatrixField 2 F1 z) 0 0) ⊤
      ((volume:Measure X).restrict ballOpens))
    (hc0 : IsCoercive (TauCeti.PDE.energyFormH1L0 ha0))
    (hFlat : ∀ z ∈ (ballOpens:Set X),coefficientMatrixField 2 F0 z = 1)
    (hInv0 : (strongDirichletOperator fixedSobolevCalculus 0 F0).IsInvertible)
    (Q : SmoothCoefficientJets 3) (f : SphereSobolev (3/2:ℝ)) :
    halfMultiplierFirstVariationL F0 F1 ha1 Q (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num) f) =
    highFirstRadialVariationL F0 F1 1 (nativeThreeHalfCoefficientMulL fixedSobolevCalculus sphereFischerInner
      orthogonalSphereHarmonics denseSphereHarmonics fixedUnitBallValueTrace Q f)-
    nativeHalfCoefficientMulL fixedSobolevCalculus sphereFischerInner orthogonalSphereHarmonics denseSphereHarmonics
      fixedUnitBallValueTrace (smoothMultiplierLowerJets Q) (highFirstRadialVariationL F0 F1 1 f) := by
  let P := strongFirstPoissonVariationL F0 F1 1
  let I0 := sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)
  let W := weakFirstPoissonVariationL 1 (coefficientMatrixField 2 F1) ha1
  let M3 := nativeThreeHalfCoefficientMulL fixedSobolevCalculus sphereFischerInner orthogonalSphereHarmonics denseSphereHarmonics fixedUnitBallValueTrace Q
  let M1 := nativeHalfCoefficientMulL fixedSobolevCalculus sphereFischerInner orthogonalSphereHarmonics denseSphereHarmonics fixedUnitBallValueTrace (smoothMultiplierLowerJets Q)
  have hBulk := strongFirstPoisson_smooth_multiplier_difference F0 F1 ha0 ha1 hc0 hFlat hInv0 Q f
  have hFirst : W (I0 f) = TauCeti.Wkp.firstOrder 1 (P f) :=
    weakFirstPoissonVariation_high_compatible F0 F1 1 (by norm_num) hFlat ha1
      (by simpa only [one_smul] using hInv0) f
  have hTrace : fixedHalfValueTraceL (TauCeti.Wkp.firstOrder 1 (P f)) = 0 := by
    have h := nativeHalfTraceL_zeroDirichlet sphereFischerInner orthogonalSphereHarmonics denseSphereHarmonics
      fixedUnitBallValueTrace ⟨W (I0 f),weakFirstPoissonVariation_mem_zero 1 ha1 (I0 f)⟩
    change fixedHalfValueTraceL (W (I0 f)) = 0 at h
    exact hFirst ▸ h
  have hProduct : fixedHalfOutwardTraceL (coefficientMultiplier fixedSobolevCalculus 2 Q (P f)) =
      M1 (fixedHalfOutwardTraceL (P f)) := by
    have h := nativeHalfOutwardTraceL_smooth_multiplier fixedSobolevCalculus sphereFischerInner orthogonalSphereHarmonics
      denseSphereHarmonics fixedUnitBallValueTrace Q (P f)
    change fixedHalfOutwardTraceL (coefficientMultiplier fixedSobolevCalculus 2 Q (P f)) =
      M1 (fixedHalfOutwardTraceL (P f))+
      nativeHalfNormalDerivativeMulL fixedSobolevCalculus sphereFischerInner orthogonalSphereHarmonics denseSphereHarmonics
        fixedUnitBallValueTrace Q (fixedHalfValueTraceL (TauCeti.Wkp.firstOrder 1 (P f))) at h
    rw [hTrace,map_zero,add_zero] at h
    exact h
  rw [halfMultiplierFirstVariation_eq_trace,ContinuousLinearMap.comp_apply,← hBulk,map_sub,hProduct]
  rfl

end ShrinkingSpheres
