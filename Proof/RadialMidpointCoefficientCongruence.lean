import Proof.ActualMidpointRadialEndpoint

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter
open scoped Topology
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.EnergyBridge OAI.AnisotropicCalderon.DirichletFamily
open OAI.AnisotropicCalderon.SphereHarmonic

/-- The true midpoint radial operator is determined by its dense high
    restriction and the coefficient inside the ball. -/
theorem midpoint_radial_eq_of_coefficient_restrictions
    (R T : SphereSobolev 1 →L[ℝ] SphereSobolev 0) (F G : SmoothCoefficientMatrix 2)
    (hField : ∀ z ∈ (ballOpens:Set X),coefficientMatrixField 2 F z = coefficientMatrixField 2 G z)
    (hR : R.comp (sphereSobolevInclusionL (3/2:ℝ) 1 (by norm_num)) =
      (sphereSobolevInclusionL (1/2:ℝ) 0 (by norm_num)).comp (actualHighRadialErrorL F))
    (hT : T.comp (sphereSobolevInclusionL (3/2:ℝ) 1 (by norm_num)) =
      (sphereSobolevInclusionL (1/2:ℝ) 0 (by norm_num)).comp (actualHighRadialErrorL G)) : R = T := by
  have hP := strongPoissonL_congr_on_ball F G hField
  have hHigh : actualHighRadialErrorL F = actualHighRadialErrorL G := by
    exact congrArg (fun Q => fixedHalfOutwardTraceL.comp Q-fixedHalfOutwardTraceL.comp fixedHarmonicLiftL) hP
  have hEq := hR.trans ((congrArg (fun Q => (sphereSobolevInclusionL (1/2:ℝ) 0 (by norm_num)).comp Q) hHigh).trans hT.symm)
  apply DFunLike.ext'
  exact (denseRange_sphereSobolevInclusionL (3/2:ℝ) 1 (by norm_num)).equalizer R.continuous T.continuous
    (funext fun u => congrArg (fun Q => Q u) hEq)

/-- Local agreement of actual coefficient families gives local agreement of
    any genuine midpoint radial families, and hence equality of their jets. -/
theorem midpoint_radial_family_germ_congr
    (R T : ℝ → SphereSobolev 1 →L[ℝ] SphereSobolev 0) (F G : ℝ → SmoothCoefficientMatrix 2)
    (hField : ∀ᶠ t in 𝓝 (0:ℝ),∀ z ∈ (ballOpens:Set X),coefficientMatrixField 2 (F t) z = coefficientMatrixField 2 (G t) z)
    (hR : ∀ᶠ t in 𝓝 (0:ℝ),(R t).comp (sphereSobolevInclusionL (3/2:ℝ) 1 (by norm_num)) =
      (sphereSobolevInclusionL (1/2:ℝ) 0 (by norm_num)).comp (actualHighRadialErrorL (F t)))
    (hT : ∀ᶠ t in 𝓝 (0:ℝ),(T t).comp (sphereSobolevInclusionL (3/2:ℝ) 1 (by norm_num)) =
      (sphereSobolevInclusionL (1/2:ℝ) 0 (by norm_num)).comp (actualHighRadialErrorL (G t))) :
    R =ᶠ[𝓝 (0:ℝ)] T := by
  filter_upwards [hField,hR,hT] with t ht hr htR
  exact midpoint_radial_eq_of_coefficient_restrictions (R t) (T t) (F t) (G t) ht hr htR

end ShrinkingSpheres
