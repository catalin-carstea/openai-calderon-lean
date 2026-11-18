import Proof.Archive.SphereSobolevSameOrderMidpoint
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1500000
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.SphereHarmonic

def negativeHalfShiftToHalf (KN : SphereSobolev (-(1/2:ℝ)) →L[ℝ] SphereSobolev (-(1/2:ℝ))) :
    SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ) :=
  (sphereSobolevBesselOrderL (-(1/2:ℝ)) (1/2:ℝ)).comp
    (KN.comp (sphereSobolevBesselOrderL (1/2:ℝ) (-(1/2:ℝ))))
def halfShiftToThreeHalf (KH : SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ)) :
    SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (3/2:ℝ) :=
  (sphereSobolevBesselOrderL (1/2:ℝ) (3/2:ℝ)).comp
    (KH.comp (sphereSobolevBesselOrderL (3/2:ℝ) (1/2:ℝ)))

lemma shifted_zero_order_compatibility
    (KN : SphereSobolev (-(1/2:ℝ)) →L[ℝ] SphereSobolev (-(1/2:ℝ)))
    (KH : SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ))
    (hc : (sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)).comp KH=
      KN.comp (sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num))) :
    (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)).comp (halfShiftToThreeHalf KH)=
      (negativeHalfShiftToHalf KN).comp (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)) := by
  have hOut := sphereSobolevBesselOrderL_inclusion_comp (1/2:ℝ) (-(1/2:ℝ)) (3/2:ℝ) (1/2:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
  have hIn := sphereSobolevBesselOrderL_inclusion_comp (3/2:ℝ) (1/2:ℝ) (1/2:ℝ) (-(1/2:ℝ))
    (by norm_num) (by norm_num) (by norm_num)
  calc
    _ = ((sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)).comp
        (sphereSobolevBesselOrderL (1/2:ℝ) (3/2:ℝ))).comp
          (KH.comp (sphereSobolevBesselOrderL (3/2:ℝ) (1/2:ℝ))) := rfl
    _ = ((sphereSobolevBesselOrderL (-(1/2:ℝ)) (1/2:ℝ)).comp
        (sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num))).comp
          (KH.comp (sphereSobolevBesselOrderL (3/2:ℝ) (1/2:ℝ))) := congrArg (fun T : SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ) => T.comp (KH.comp (sphereSobolevBesselOrderL (3/2:ℝ) (1/2:ℝ)))) hOut
    _ = (sphereSobolevBesselOrderL (-(1/2:ℝ)) (1/2:ℝ)).comp
        (((sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)).comp KH).comp
          (sphereSobolevBesselOrderL (3/2:ℝ) (1/2:ℝ))) := rfl
    _ = (sphereSobolevBesselOrderL (-(1/2:ℝ)) (1/2:ℝ)).comp
        ((KN.comp (sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num))).comp
          (sphereSobolevBesselOrderL (3/2:ℝ) (1/2:ℝ))) := congrArg (fun T : SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ)) => (sphereSobolevBesselOrderL (-(1/2:ℝ)) (1/2:ℝ)).comp (T.comp (sphereSobolevBesselOrderL (3/2:ℝ) (1/2:ℝ)))) hc
    _ = (sphereSobolevBesselOrderL (-(1/2:ℝ)) (1/2:ℝ)).comp
        (KN.comp ((sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)).comp
          (sphereSobolevBesselOrderL (3/2:ℝ) (1/2:ℝ)))) := rfl
    _ = (sphereSobolevBesselOrderL (-(1/2:ℝ)) (1/2:ℝ)).comp
        (KN.comp ((sphereSobolevBesselOrderL (1/2:ℝ) (-(1/2:ℝ))).comp
          (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)))) := congrArg (fun T : SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ)) => (sphereSobolevBesselOrderL (-(1/2:ℝ)) (1/2:ℝ)).comp (KN.comp T)) hIn
    _ = _ := rfl

def zeroOrderMidpointL (KN : SphereSobolev (-(1/2:ℝ)) →L[ℝ] SphereSobolev (-(1/2:ℝ)))
    (KH : SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ))
    (hc : (sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)).comp KH=
      KN.comp (sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num))) :
    SphereSobolev 0 →L[ℝ] SphereSobolev 0 :=
  (sphereSobolevBesselOrderL 1 0).comp
    ((sphereSobolevSameOrderMidpointL (negativeHalfShiftToHalf KN) (halfShiftToThreeHalf KH)
      (shifted_zero_order_compatibility KN KH hc)).comp (sphereSobolevBesselOrderL 0 1))
end ShrinkingSpheres
