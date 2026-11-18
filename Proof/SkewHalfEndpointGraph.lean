import Proof.SkewNegativeHalfCompatibility
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped InnerProductSpace
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.SphereHarmonic

/-- The positive-half endpoint furnished by the public skew compatibility
square realizes the SAME coarse physical operator. -/
lemma skew_negative_half_endpoint_graph (T : SphereSobolev 1 →L[ℝ] SphereSobolev 0)
    (KN : SphereSobolev (-(1/2:ℝ)) →L[ℝ] SphereSobolev (-(1/2:ℝ)))
    (hSkew : ∀ u v : SphereSobolev 1,
      ⟪T u,sphereSobolevInclusionL 1 0 (by norm_num) v⟫_ℝ=
        -⟪sphereSobolevInclusionL 1 0 (by norm_num) u,T v⟫_ℝ)
    (hGraph : (sphereSobolevInclusionL 0 (-(1/2:ℝ)) (by norm_num)).comp T=
      KN.comp (sphereSobolevInclusionL 1 (-(1/2:ℝ)) (by norm_num))) :
    (sphereSobolevInclusionL (1/2:ℝ) 0 (by norm_num)).comp
      ((-KN.adjoint : SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ)).comp
        (sphereSobolevInclusionL 1 (1/2:ℝ) (by norm_num)))=T := by
  have hc := negative_skew_half_compatible T KN hSkew hGraph
  apply ContinuousLinearMap.ext
  intro u
  apply sphereSobolevInclusionL_injective 0 (-(1/2:ℝ)) (by norm_num)
  have hh := DFunLike.congr_fun hc (sphereSobolevInclusionL 1 (1/2:ℝ) (by norm_num) u)
  have hg := DFunLike.congr_fun hGraph u
  change sphereSobolevInclusionL 0 (-(1/2:ℝ)) (by norm_num)
    (sphereSobolevInclusionL (1/2:ℝ) 0 (by norm_num)
      (-KN.adjoint (sphereSobolevInclusionL 1 (1/2:ℝ) (by norm_num) u)))=_
  rw [sphereSobolevInclusionL_trans_apply]
  exact hh.trans ((congrArg KN (sphereSobolevInclusionL_trans_apply _ _ _ _ _ _)).trans hg.symm)
end ShrinkingSpheres
