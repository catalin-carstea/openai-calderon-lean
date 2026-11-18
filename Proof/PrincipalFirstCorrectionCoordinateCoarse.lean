import Proof.PrincipalFirstCorrectionCoordinateContraction

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
open Set
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.SphereHarmonic

def principalFirstCorrectionCoordinateCoarseL (d : Data) (b : I) (x : X) :
    SphereSobolev 1 →L[ℝ] SphereSobolev 0 :=
  ∑ a : I,principalFirstErrorCoordinateWeight d a b x • physicalFirstCorrectionCoarseFamily d (axis a) x

lemma principalFirstCorrectionCoordinate_coarse_low_compatible (d : Data) (x : X)
    (hFrame : ∀ i j,metricPair d.γ x (d.frame x i) (d.frame x j)=if i=j then 1 else 0) (b : I) :
    (sphereSobolevInclusionL 0 (-(1/2:ℝ)) (by norm_num)).comp
      (principalFirstCorrectionCoordinateCoarseL d b x)=
      (principalFirstCorrectionCoordinateHalfL d x b).comp
        (sphereSobolevInclusionL 1 (1/2:ℝ) (by norm_num)) := by
  rw [principalFirstCorrectionCoordinateHalfL_eq d x hFrame b]
  apply ContinuousLinearMap.ext
  intro u
  have hLow (a : I) := DFunLike.congr_fun (physicalFirstCorrectionHalfL_coarse d x (axis a)) u
  simp only [ContinuousLinearMap.comp_apply] at hLow
  simp only [principalFirstCorrectionCoordinateCoarseL,ContinuousLinearMap.comp_apply,
    _root_.sum_apply,_root_.smul_apply,map_sum,map_smul,hLow]

lemma principalFirstCorrectionCoordinate_coarse_high_compatible (d : Data) (x : X) (b : I) :
    (sphereSobolevInclusionL (1/2:ℝ) 0 (by norm_num)).comp
      (principalFirstCorrectionCoordinateHigherL d x b)=
      (principalFirstCorrectionCoordinateCoarseL d b x).comp
        (sphereSobolevInclusionL (3/2:ℝ) 1 (by norm_num)) := by
  apply ContinuousLinearMap.ext
  intro u
  have hHigh (a : I) := DFunLike.congr_fun (physicalFirstCorrectionHigherL_coarse d x (axis a)) u
  simp only [ContinuousLinearMap.comp_apply] at hHigh
  simp only [principalFirstCorrectionCoordinateCoarseL,principalFirstCorrectionCoordinateHigherL,
    ContinuousLinearMap.comp_apply,_root_.sum_apply,_root_.smul_apply,map_sum,map_smul,hHigh]

end ShrinkingSpheres
