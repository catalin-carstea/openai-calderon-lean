import Proof.StrongBoundaryMultiplierDefect
import Proof.Archive.NativeOrderOneCoefficientMultiplier
import Proof.Archive.NativeH2OrthogonalPullbackExistence

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000
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
attribute [local instance] TauCeti.W1p0.instNormedAddCommGroup TauCeti.W1p0.instInnerProductSpace
attribute [local irreducible] functionalInverse nativeZeroFunctionalInverse nativeCoefficientWeakFunctionalInverse

/-- The actual H2 Poisson multiplication difference is the SAME strong
inverse forcing defect, on its full high boundary domain. -/
theorem strongPoisson_smooth_multiplier_difference (F : SmoothCoefficientMatrix 2)
    (ha : MemLp (fun z => TauCeti.PDE.energyIntegrand (coefficientMatrixField 2 F z) 0 0) ⊤
      ((volume:Measure X).restrict ballOpens))
    (hc : IsCoercive (TauCeti.PDE.energyFormH1L0 ha))
    (hInv : (strongDirichletOperator fixedSobolevCalculus 0 F).IsInvertible)
    (Q : SmoothCoefficientJets 3) (f : SphereSobolev (3/2:ℝ)) :
    strongPoissonL F (nativeThreeHalfCoefficientMulL fixedSobolevCalculus sphereFischerInner orthogonalSphereHarmonics
      denseSphereHarmonics fixedUnitBallValueTrace Q f)-
      coefficientMultiplier fixedSobolevCalculus 2 Q (strongPoissonL F f) =
    strongPoissonMultiplierDefectL F ha Q (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num) f) := by
  let P := strongPoissonL F
  let W := nativeWeakHalfLift (coefficientMatrixField 2 F) 0 0 ha sphereFischerInner
  let V := strongPoissonMultiplierDefectL F ha Q
  let I0 := sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)
  let J : BallSobolev 2 →L[ℝ] BallH1 := TauCeti.Wkp.firstOrderL 1
  let S := nativeCoefficientH1ProductL fixedSobolevCalculus (smoothMultiplierLowerJets Q)
  let M3 := nativeThreeHalfCoefficientMulL fixedSobolevCalculus sphereFischerInner orthogonalSphereHarmonics denseSphereHarmonics fixedUnitBallValueTrace Q
  let M1 := nativeHalfCoefficientMulL fixedSobolevCalculus sphereFischerInner orthogonalSphereHarmonics denseSphereHarmonics fixedUnitBallValueTrace (smoothMultiplierLowerJets Q)
  have hP (v : SphereSobolev (3/2:ℝ)) : J (P v) = W (I0 v) := by
    change TauCeti.Wkp.firstOrder 1 (strongPoissonL F v) =
      nativeWeakHalfLift (coefficientMatrixField 2 F) 0 0 ha sphereFischerInner (I0 v)
    exact (nativeWeakHalfLift_eq_strongPoisson ha hc F (fun z _ => rfl) hInv v).symm
  have hV : J (V (I0 f)) = W (M1 (I0 f))-S (W (I0 f)) :=
    firstOrder_strongPoissonMultiplierDefect F ha hc hInv Q (I0 f)
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

end ShrinkingSpheres
