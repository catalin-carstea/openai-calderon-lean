import Proof.DenseOperatorRestrictionUnique
import Proof.ActualRadialTaylorEndpoints
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxSynthPendingDepth 30
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.SphereHarmonic
lemma coarse_rotation_generator_unique (A C D : SphereSobolev 1 →L[ℝ] SphereSobolev 0) (i j : I)
    (hC : ∀ f : SphereSobolev 2,
      sphereSobolevRotationL 0 i j (A (sphereSobolevInclusionL 2 1 (by norm_num) f)) =
        sphereSobolevInclusionL 0 (-1) (by norm_num)
          (C (sphereSobolevInclusionL 2 1 (by norm_num) f)+A (sphereSobolevRotationL 2 i j f)))
    (hD : ∀ f : SphereSobolev 2,
      sphereSobolevRotationL 0 i j (A (sphereSobolevInclusionL 2 1 (by norm_num) f)) =
        sphereSobolevInclusionL 0 (-1) (by norm_num)
          (D (sphereSobolevInclusionL 2 1 (by norm_num) f)+A (sphereSobolevRotationL 2 i j f))) : C=D := by
  apply clm_eq_of_dense_restriction (sphereSobolevInclusionL 2 1 (by norm_num))
    (denseRange_sphereSobolevInclusionL 2 1 (by norm_num))
  apply ContinuousLinearMap.ext
  intro f
  exact add_right_cancel ((sphereSobolevInclusionL_injective 0 (-1) (by norm_num)) ((hC f).symm.trans (hD f)))
end ShrinkingSpheres
