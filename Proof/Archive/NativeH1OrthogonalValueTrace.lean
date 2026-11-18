import Proof.Archive.NativeSphereL2OrthogonalPullback
import Proof.Archive.NativeH1OrthogonalPullback
import Proof.Archive.NativeGlobalSmoothH1Density
import Proof.Archive.NativeValueRadialTrace

set_option autoImplicit false
noncomputable section
open Set MeasureTheory
open scoped ENNReal ContDiff
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge SphereHarmonic SmoothAngularCasimir

 

lemma valueTraceL_nativeH1OrthogonalPullback (τ0 : UnitBallValueTrace)
    (e : R3 ≃ₗᵢ[ℝ] R3) (u : BallH1) :
    τ0.valueTraceL (nativeH1OrthogonalPullback e u) =
      sphereL2OrthogonalPullback e (τ0.valueTraceL u) := by
  let A : BallH1 →L[ℝ] SphereL2 := τ0.valueTraceL.comp (nativeH1OrthogonalPullback e).toContinuousLinearMap
  let C : BallH1 →L[ℝ] SphereL2 := (sphereL2OrthogonalPullback e).toContinuousLinearMap.comp τ0.valueTraceL
  have hEq : (A : BallH1 → SphereL2) = C := by
    apply denseRange_smoothSobolev.equalizer A.continuous C.continuous
    funext f
    change τ0.valueTraceL (nativeH1OrthogonalPullback e (smoothSobolev f)) =
      sphereL2OrthogonalPullback e (τ0.valueTraceL (smoothSobolev f))
    rw [nativeH1OrthogonalPullback_smoothSobolev,τ0.valueTrace_smooth,τ0.valueTrace_smooth]
    exact (sphereL2OrthogonalPullback_smoothSphereLift e f).symm
  exact congr_fun hEq u

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

