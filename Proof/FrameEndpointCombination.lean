import Proof.ActualFrameFirstAdjointError
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option maxSynthPendingDepth 30
open Set
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.SphereHarmonic

/-- Shared exact low endpoint combination, extracted from the existing
    frame producer for that caller and the actual frame raising commutator. -/
lemma frame_low_endpoint_combination (d : Data)
    (A : X → SphereSobolev 1 →L[ℝ] SphereSobolev 0)
    (G : I → X → SphereSobolev 1 →L[ℝ] SphereSobolev 0) (i : I) (x : X)
    (Lo : I → SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ)))
    (hLo : ∀ a,(sphereSobolevInclusionL 0 (-(1/2:ℝ)) (by norm_num)).comp
      (actualFirstAdjointErrorFamily d (axis a) A (G a) x)=
        (Lo a).comp (sphereSobolevInclusionL 1 (1/2:ℝ) (by norm_num))) :
    (sphereSobolevInclusionL 0 (-(1/2:ℝ)) (by norm_num)).comp (actualFrameFirstAdjointErrorFamily d A G i x)=
      (∑ a : I,d.frame x i a • Lo a).comp (sphereSobolevInclusionL 1 (1/2:ℝ) (by norm_num)) := by
  apply ContinuousLinearMap.ext
  intro u
  simp only [actualFrameFirstAdjointErrorFamily,ContinuousLinearMap.comp_apply,
    _root_.sum_apply,_root_.smul_apply,map_sum,map_smul]
  apply Finset.sum_congr rfl
  intro a _
  exact congrArg (fun v => d.frame x i a • v) (DFunLike.congr_fun (hLo a) u)

/-- Shared exact higher endpoint combination for the SAME frame error. -/
lemma frame_high_endpoint_combination (d : Data)
    (A : X → SphereSobolev 1 →L[ℝ] SphereSobolev 0)
    (G : I → X → SphereSobolev 1 →L[ℝ] SphereSobolev 0) (i : I) (x : X)
    (Hi : I → SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ))
    (hHi : ∀ a,(sphereSobolevInclusionL (1/2:ℝ) 0 (by norm_num)).comp (Hi a)=
      (actualFirstAdjointErrorFamily d (axis a) A (G a) x).comp
        (sphereSobolevInclusionL (3/2:ℝ) 1 (by norm_num))) :
    (sphereSobolevInclusionL (1/2:ℝ) 0 (by norm_num)).comp (∑ a : I,d.frame x i a • Hi a)=
      (actualFrameFirstAdjointErrorFamily d A G i x).comp (sphereSobolevInclusionL (3/2:ℝ) 1 (by norm_num)) := by
  apply ContinuousLinearMap.ext
  intro u
  simp only [actualFrameFirstAdjointErrorFamily,ContinuousLinearMap.comp_apply,
    _root_.sum_apply,_root_.smul_apply,map_sum,map_smul]
  apply Finset.sum_congr rfl
  intro a _
  exact congrArg (fun v => d.frame x i a • v) (DFunLike.congr_fun (hHi a) u)
end ShrinkingSpheres
