import Proof.ActualRadialTaylorEndpoints
import Proof.SphereSobolevOperatorExt
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1400000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.SphereHarmonic

/-- Compatibility on a common dense high domain identifies the midpoint
    with the SAME weak half endpoint on its entire H1 domain. -/
lemma midpoint_half_compatible_of_common_high
    (R : SphereSobolev 1 →L[ℝ] SphereSobolev 0)
    (L : SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ)))
    (H : SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ))
    (hRH : (sphereSobolevInclusionL (1/2:ℝ) 0 (by norm_num)).comp H =
      R.comp (sphereSobolevInclusionL (3/2:ℝ) 1 (by norm_num)))
    (hLH : (sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)).comp H =
      L.comp (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num))) :
    (sphereSobolevInclusionL 0 (-(1/2:ℝ)) (by norm_num)).comp R =
      L.comp (sphereSobolevInclusionL 1 (1/2:ℝ) (by norm_num)) := by
  let A := (sphereSobolevInclusionL 0 (-(1/2:ℝ)) (by norm_num)).comp R
  let B := L.comp (sphereSobolevInclusionL 1 (1/2:ℝ) (by norm_num))
  have hPre (v : SphereSobolev (3/2:ℝ)) :
      A (sphereSobolevInclusionL (3/2:ℝ) 1 (by norm_num) v) =
        B (sphereSobolevInclusionL (3/2:ℝ) 1 (by norm_num) v) := by
    have hR := congrArg (fun T : SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev 0 => T v) hRH
    have hL := congrArg (fun T : SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ)) => T v) hLH
    simp only [ContinuousLinearMap.comp_apply] at hR hL
    change sphereSobolevInclusionL 0 (-(1/2:ℝ)) (by norm_num)
      (R (sphereSobolevInclusionL (3/2:ℝ) 1 (by norm_num) v)) = _
    rw [← hR,sphereSobolevInclusionL_trans_apply,hL]
    exact congrArg L (sphereSobolevInclusionL_trans_apply (3/2:ℝ) 1 (1/2:ℝ) (by norm_num) (by norm_num) v).symm
  have hEq : (fun u => A u) = (fun u => B u) :=
    (denseRange_sphereSobolevInclusionL (3/2:ℝ) 1 (by norm_num)).equalizer A.continuous B.continuous (funext hPre)
  exact ContinuousLinearMap.ext (fun u => congr_fun hEq u)
end ShrinkingSpheres
