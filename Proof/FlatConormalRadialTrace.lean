import Proof.WeakConormalStrongTrace
import Proof.WeakPoissonComparison
import Proof.UniformWeakConormalComparison

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxSynthPendingDepth 15
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set MeasureTheory
open scoped ENNReal
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.EnergyBridge OAI.AnisotropicCalderon.DirichletFamily
open OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open OAI.AnisotropicCalderon.SphereHarmonic OAI.AnisotropicCalderon.SpectralCoreRegularity

/-- For a scalar Euclidean coefficient the conormal is exactly that scalar
    times the outward radial derivative; compact exterior extensions do not matter. -/
theorem ordinaryConormalTraceL_flat (F : SmoothCoefficientMatrix 2) (c : ℝ)
    (hF : ∀ x ∈ (ballOpens : Set X),coefficientMatrixField 2 F x = c • (1:Mat))
    (U : BallSobolev 2) :
    ordinaryConormalTraceL fixedSobolevCalculus fixedUnitBallValueTrace F U =
      c • outwardRadialTraceL fixedSobolevCalculus fixedUnitBallValueTrace U := by
  have hMult (i j : I) : coefficientMultiplier fixedSobolevCalculus 1 (F i j) =
      (if i=j then c else 0) • ContinuousLinearMap.id ℝ (BallSobolev 1) := by
    apply coefficientMultiplier_eq_const_of_on_ball
    intro x hx
    have hh := congrArg (fun A : Mat => A i j) (hF x hx)
    simpa only [coefficientMatrixField,Matrix.smul_apply,Matrix.one_apply,smul_eq_mul,mul_ite,mul_one,mul_zero] using hh
  rw [ordinaryConormalTraceL_apply,outwardRadialTraceL_apply,Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  calc
    _ = ∑ j : I,if j=i then c • sphereCoordinateMulL i
        (fixedUnitBallValueTrace.valueTraceL (TauCeti.Wkp.firstOrder 0
          (unitBallCoordinateDerivativeL fixedSobolevCalculus 1 i U))) else 0 := by
      apply Finset.sum_congr rfl
      intro j hj
      by_cases h : i=j
      · subst j
        simp only [hMult,ite_true,ContinuousLinearMap.smul_apply,ContinuousLinearMap.id_apply,
          TauCeti.Wkp.firstOrder_zero,map_smul]
      · simp only [hMult,if_neg h,if_neg (Ne.symm h),zero_smul,
          ContinuousLinearMap.zero_apply]
        have hZ : TauCeti.Wkp.firstOrder 0 (0 : BallSobolev 1) = (0 : BallH1) :=
          (TauCeti.Wkp.firstOrderL (mu:=(volume:Measure X)) (Omega:=ballOpens) (p:=2) 0).map_zero
        rw [hZ,fixedUnitBallValueTrace.valueTraceL.map_zero,(sphereCoordinateMulL i).map_zero]
    _ = _ := by simp

/-- The flat weak endpoint agrees with the genuine completed radial derivative
    on H3/2 data, with its actual scalar coefficient. -/
theorem nativeWeakConormal_flat_high (c : ℝ) (f : SphereSobolev (3/2:ℝ)) :
    nativeWeakConormalEndpoint (fun _ : X => c • (1:Mat)) (fun _ => (0:X)) (fun _ => (0:ℝ))
      (flatCoefficientBound c) sphereFischerInner
      (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num) f) =
    c • sphereSobolevInclusionL 0 (-(1/2:ℝ)) (by norm_num)
      (sphereSobolevZeroEquiv orthogonalSphereHarmonics denseSphereHarmonics
        (outwardRadialTraceL fixedSobolevCalculus fixedUnitBallValueTrace (fixedHarmonicLiftL f))) := by
  obtain ⟨F0,hF0⟩ := exists_flatCoefficientMatrix 2
  have hFlat (x : X) (hx : x ∈ (ballOpens : Set X)) : coefficientMatrixField 2 F0 x = 1 :=
    hF0 x (unitBall_subset_closedBall_two hx)
  have hPoint (x : X) (hx : x ∈ (ballOpens : Set X)) :
      coefficientMatrixField 2 (c • F0) x = c • (1:Mat) := by
    rw [coefficientMatrixField_smul,hFlat x hx]
  have hLift := congrArg (fun T : SphereSobolev (1/2:ℝ) →L[ℝ] BallH1 =>
      T (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num) f))
    (nativeWeakHalfLift_flat_eq c (flatCoefficientBound c))
  have hOrder := OAI.AnisotropicCalderon.NativeHarmonicLiftOrderCoherence.firstOrder_harmonicLiftCompletion
    sphereFischerInner orthogonalSphereHarmonics f
  have hHarm : ordinaryPrincipalL fixedSobolevCalculus 0 (c • F0) (fixedHarmonicLiftL f) = 0 :=
    fullCoefficientOperator_flat_harmonicLift fixedSobolevCalculus sphereFischerInner
      orthogonalSphereHarmonics F0 hFlat c f
  have h := nativeWeakConormal_eq_ordinary_trace (flatCoefficientBound c) (c • F0) hPoint
    (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num) f)
    (fixedHarmonicLiftL f) (hLift.trans hOrder.symm) hHarm
  rw [ordinaryConormalTraceL_flat (c • F0) c hPoint,map_smul,map_smul] at h
  exact h

/-- A fixed bounded low-endpoint Euclidean radial map. -/
def fixedLowRadialL : SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ)) :=
  nativeWeakConormalEndpoint (fun _ : X => (1:ℝ) • (1:Mat)) (fun _ => (0:X)) (fun _ => (0:ℝ))
    (flatCoefficientBound 1) sphereFischerInner

theorem fixedLowRadialL_high (f : SphereSobolev (3/2:ℝ)) :
    fixedLowRadialL (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num) f) =
      sphereSobolevInclusionL 0 (-(1/2:ℝ)) (by norm_num)
        (sphereSobolevZeroEquiv orthogonalSphereHarmonics denseSphereHarmonics
          (outwardRadialTraceL fixedSobolevCalculus fixedUnitBallValueTrace (fixedHarmonicLiftL f))) := by
  simpa only [fixedLowRadialL,one_smul] using nativeWeakConormal_flat_high 1 f

theorem nativeWeakConormal_flat_eq_smul (c : ℝ) :
    nativeWeakConormalEndpoint (fun _ : X => c • (1:Mat)) (fun _ => (0:X)) (fun _ => (0:ℝ))
      (flatCoefficientBound c) sphereFischerInner = c • fixedLowRadialL := by
  have he : (nativeWeakConormalEndpoint (fun _ : X => c • (1:Mat)) (fun _ => (0:X))
      (fun _ => (0:ℝ)) (flatCoefficientBound c) sphereFischerInner :
      SphereSobolev (1/2:ℝ) → SphereSobolev (-(1/2:ℝ))) =
      (c • fixedLowRadialL : SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ))) := by
    apply (denseRange_sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)).equalizer
      (ContinuousLinearMap.continuous _) (ContinuousLinearMap.continuous _)
    funext f
    exact (nativeWeakConormal_flat_high c f).trans
      (congrArg (fun z => c • z) (fixedLowRadialL_high f).symm)
  exact DFunLike.ext' he

end ShrinkingSpheres
