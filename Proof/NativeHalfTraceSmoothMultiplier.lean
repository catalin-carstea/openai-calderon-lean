import Proof.Archive.NativeSmoothMultiplicationTrace
import Proof.Archive.NativeHalfSmoothMultiplier
import Proof.Archive.NativeFullSharpHalfTrace
set_option autoImplicit false
noncomputable section
open Set MeasureTheory
open scoped ENNReal Gradient
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge ConnectionError SphereHarmonic NativeHalfSmoothMultiplier
  NativeFullSharpHalfTrace

theorem nativeHalfTraceL_contDiffSMulL
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics)
    (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (m : SmoothData) {M : ℝ} (hM : 0 ≤ M)
    (hm : ∀ x ∈ (ballOpens : Set R3), |m.1 x| ≤ M)
    (hg : ∀ x ∈ (ballOpens : Set R3), ‖gradient m.1 x‖ ≤ M)
    (u : BallH1) :
    nativeHalfTraceL hF hO hD τ0
      (TauCeti.W1p.contDiffSMulL (mu := (volume : Measure R3)) (Omega := ballOpens)
        (p := 2) m.1 m.2 hM hm hg u) =
      nativeHalfSmoothMulL hF hO hD τ0 m hM hm hg
        (nativeHalfTraceL hF hO hD τ0 u) := by
  let I : SphereSobolev (1/2 : ℝ) →L[ℝ] SphereSobolev 0 :=
    sphereSobolevInclusionL (1/2 : ℝ) 0 (by norm_num)
  let Z : SphereL2 ≃ₗᵢ[ℝ] SphereSobolev 0 := sphereSobolevZeroEquiv hO hD
  let T : BallH1 →L[ℝ] SphereSobolev (1/2 : ℝ) := nativeHalfTraceL hF hO hD τ0
  let S : BallH1 →L[ℝ] BallH1 := TauCeti.W1p.contDiffSMulL
    (mu := (volume : Measure R3)) (Omega := ballOpens) (p := 2) m.1 m.2 hM hm hg
  let Mq : SphereSobolev (1/2 : ℝ) →L[ℝ] SphereSobolev (1/2 : ℝ) :=
    nativeHalfSmoothMulL hF hO hD τ0 m hM hm hg
  let Cq : SphereL2 →L[ℝ] SphereL2 := sphereContinuousScalarMulL (smoothSphereValue m)
  have ht (v : BallH1) : I (T v) = Z (τ0.valueTraceL v) :=
    sphereSobolevInclusionL_nativeHalfTraceL hF hO hD τ0 v
  have hbulk : τ0.valueTraceL (S u) = Cq (τ0.valueTraceL u) :=
    valueTraceL_contDiffSMulL τ0 m hM hm hg u
  have hmul : I (Mq (T u)) = Z (Cq (Z.symm (I (T u)))) :=
    sphereSobolevInclusionL_nativeHalfSmoothMulL hF hO hD τ0 m hM hm hg (T u)
  have hin : Z.symm (I (T u)) = τ0.valueTraceL u :=
    (congrArg (fun v : SphereSobolev 0 => Z.symm v) (ht u)).trans
      (Z.symm_apply_apply (τ0.valueTraceL u))
  have hr : I (Mq (T u)) = Z (Cq (τ0.valueTraceL u)) :=
    hmul.trans (congrArg (fun v : SphereL2 => Z (Cq v)) hin)
  apply sphereSobolevInclusionL_injective (1/2 : ℝ) 0 (by norm_num)
  change I (T (S u)) = I (Mq (T u))
  exact (ht (S u)).trans ((congrArg Z hbulk).trans hr.symm)


end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
