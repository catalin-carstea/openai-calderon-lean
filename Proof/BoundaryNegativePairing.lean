import Proof.EndpointBoundaryCalculus
import Proof.Archive.SphereSobolevPairingInclusion

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 700000
set_option maxSynthPendingDepth 15
open scoped InnerProductSpace
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.EnergyBridge OAI.AnisotropicCalderon.DirichletFamily
open OAI.AnisotropicCalderon.SphereHarmonic

/-- The spectral negative-half inclusion has the actual normalized L2 pairing. -/
theorem boundary_negative_pairing (z h : SphereSobolev (1/2:ℝ)) (v w : SphereL2)
    (hh : sphereSobolevInclusionL (1/2:ℝ) 0 (by norm_num) h =
      sphereSobolevZeroEquiv orthogonalSphereHarmonics denseSphereHarmonics v)
    (hz : sphereSobolevInclusionL (1/2:ℝ) 0 (by norm_num) z =
      sphereSobolevZeroEquiv orthogonalSphereHarmonics denseSphereHarmonics w) :
    sphereSobolevDualPairing (1/2:ℝ) z
      (sphereSobolevInclusionL 0 (-(1/2:ℝ)) (by norm_num)
        (sphereSobolevZeroEquiv orthogonalSphereHarmonics denseSphereHarmonics v)) = ⟪v,w⟫_ℝ := by
  have hTrans := congrArg (fun T : SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ)) => T h)
    (sphereSobolevInclusionL_trans (1/2:ℝ) 0 (-(1/2:ℝ)) (by norm_num) (by norm_num))
  simp only [ContinuousLinearMap.comp_apply] at hTrans
  rw [hh] at hTrans
  rw [hTrans]
  have hp := sphereSobolevDualPairing_inclusion_eq_inner_zero (1/2:ℝ) (by norm_num) h z
  have hs : sphereSobolevDualPairing (1/2:ℝ) z
      (sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num) h) =
      ⟪sphereSobolevInclusionL (1/2:ℝ) 0 (by norm_num) h,
        sphereSobolevInclusionL (1/2:ℝ) 0 (by norm_num) z⟫_ℝ :=
    (real_inner_comm _ _).trans hp
  rw [hh,hz] at hs
  exact hs.trans ((sphereSobolevZeroEquiv orthogonalSphereHarmonics denseSphereHarmonics).inner_map_map v w)

end ShrinkingSpheres
