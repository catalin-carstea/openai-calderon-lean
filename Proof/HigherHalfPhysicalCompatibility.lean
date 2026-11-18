import Proof.HalfDegreeHigherLift
import Proof.CoarseRotationAdjointPairing
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1400000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.SphereHarmonic

lemma higher_half_coarse_compatible_of_blocks
    (R : SphereSobolev 1 →L[ℝ] SphereSobolev 0)
    (H : SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ))
    (hH : ∀ m n : ℕ,∀ z : harmonicSphereSubspace n,
      sphereSobolevCoefficientL (1/2:ℝ) m (H (sphereSobolevSingleL (3/2:ℝ) n z)) =
        coarsePhysicalHarmonicBlock R m n z) :
    (sphereSobolevInclusionL (1/2:ℝ) 0 (by norm_num)).comp H =
      R.comp (sphereSobolevInclusionL (3/2:ℝ) 1 (by norm_num)) := by
  apply sphereSobolev_clm_ext_on_single (3/2:ℝ)
  intro n z
  apply sphereSobolev_ext 0
  intro m
  simp only [ContinuousLinearMap.comp_apply,sphereSobolevCoefficientL_inclusion,sphereSobolevInclusionL_single]
  exact hH m n z
end ShrinkingSpheres
