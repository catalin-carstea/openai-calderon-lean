import Proof.BalancedDegreeCommutator

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.SphereHarmonic

/-- A genuine balanced higher realization of the SAME low endpoint is
compatible with its genuine coarse realization. Only inclusion graphs and
injectivity are used, never equality of normalized Sobolev carrier types. -/
lemma balanced_endpoint_high_of_coarse_low
    (E : SphereSobolev 1 →L[ℝ] SphereSobolev 0)
    (Lo : SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ)))
    (Hi : SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ))
    (hLo : (sphereSobolevInclusionL 0 (-(1/2:ℝ)) (by norm_num)).comp E=
      Lo.comp (sphereSobolevInclusionL 1 (1/2:ℝ) (by norm_num)))
    (hPair : (sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)).comp Hi=
      Lo.comp (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num))) :
    (sphereSobolevInclusionL (1/2:ℝ) 0 (by norm_num)).comp Hi=
      E.comp (sphereSobolevInclusionL (3/2:ℝ) 1 (by norm_num)) := by
  apply ContinuousLinearMap.ext
  intro u
  apply sphereSobolevInclusionL_injective 0 (-(1/2:ℝ)) (by norm_num)
  have hH := DFunLike.congr_fun hPair u
  have hL := DFunLike.congr_fun hLo (sphereSobolevInclusionL (3/2:ℝ) 1 (by norm_num) u)
  simp only [ContinuousLinearMap.comp_apply,sphereSobolevInclusionL_trans_apply] at hH hL ⊢
  exact hH.trans hL.symm

end ShrinkingSpheres
