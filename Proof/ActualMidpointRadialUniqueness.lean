import Proof.RadialMidpointCoefficientCongruence
import Proof.ActualMidpointRadialEndpoint

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxSynthPendingDepth 20
open Set
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.EnergyBridge OAI.AnisotropicCalderon.DirichletFamily
open OAI.AnisotropicCalderon.SphereHarmonic OAI.AnisotropicCalderon.SpectralCoreRegularity

/-- The actual midpoint radial error is specified by its genuine strong
    response on the dense high-regularity boundary data, independently of cutoff. -/
def RealizesActualMidpointRadialError (d : Data) (y : X)
    (R : SphereSobolev 1 →L[ℝ] SphereSobolev 0) : Prop :=
  ∀ F : SmoothCoefficientMatrix 2,
    (∀ z ∈ (ballOpens : Set X),coefficientMatrixField 2 F z =
      principalCoefficient (framedNormalMetric d.g₁ d.frame d.expMap y (d.radius y)) z) →
    R.comp (sphereSobolevInclusionL (3/2:ℝ) 1 (by norm_num)) =
      (sphereSobolevInclusionL (1/2:ℝ) 0 (by norm_num)).comp (actualHighRadialErrorL F)

lemma realizesActualMidpointRadialError_of_restriction (d : Data) (y : X)
    (R : SphereSobolev 1 →L[ℝ] SphereSobolev 0) (F0 : SmoothCoefficientMatrix 2)
    (hF0 : ∀ z ∈ (ballOpens : Set X),coefficientMatrixField 2 F0 z =
      principalCoefficient (framedNormalMetric d.g₁ d.frame d.expMap y (d.radius y)) z)
    (hR : R.comp (sphereSobolevInclusionL (3/2:ℝ) 1 (by norm_num)) =
      (sphereSobolevInclusionL (1/2:ℝ) 0 (by norm_num)).comp (actualHighRadialErrorL F0)) :
    RealizesActualMidpointRadialError d y R := by
  intro F hF
  have hPoisson := strongPoissonL_congr_on_ball F0 F (fun z hz => (hF0 z hz).trans (hF z hz).symm)
  have hHigh : actualHighRadialErrorL F0 = actualHighRadialErrorL F :=
    congrArg (fun Q => fixedHalfOutwardTraceL.comp Q-fixedHalfOutwardTraceL.comp fixedHarmonicLiftL) hPoisson
  exact hR.trans (congrArg (fun Q => (sphereSobolevInclusionL (1/2:ℝ) 0 (by norm_num)).comp Q) hHigh)

lemma RealizesActualMidpointRadialError.unique (d : Data) (y : X)
    (R T : SphereSobolev 1 →L[ℝ] SphereSobolev 0)
    (hR : RealizesActualMidpointRadialError d y R) (hT : RealizesActualMidpointRadialError d y T)
    (F : SmoothCoefficientMatrix 2)
    (hF : ∀ z ∈ (ballOpens : Set X),coefficientMatrixField 2 F z =
      principalCoefficient (framedNormalMetric d.g₁ d.frame d.expMap y (d.radius y)) z) : R = T := by
  exact midpoint_radial_eq_of_coefficient_restrictions R T F F (fun _ _ => rfl) (hR F hF) (hT F hF)

end ShrinkingSpheres
