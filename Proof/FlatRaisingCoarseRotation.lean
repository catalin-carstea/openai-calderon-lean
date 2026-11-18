import Proof.GradedRaisingRotation
import Proof.FrameErrorRaisingHalfCross
import Proof.RightMultiplierRotationGraph
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
open Set
open scoped ContDiff Topology
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.SphereHarmonic

def flatOneRaisingL (i : I) : SphereSobolev 1 →L[ℝ] SphereSobolev 0 := flatRaisingSobolevL 1 i

def flatRaisingRotationCommutatorL (i j a : I) : SphereSobolev 1 →L[ℝ] SphereSobolev 0 :=
  (if a=j then flatOneRaisingL i else 0)-(if a=i then flatOneRaisingL j else 0)

/-- The exact rotation graph for flat raising uses a genuine common H2
    core and distributional H(-1) output, without unbounded selfmaps. -/
lemma flatOneRaisingL_coarse_rotation (i j a : I) (u : SphereSobolev 2) :
    sphereSobolevRotationL 0 i j (flatOneRaisingL a (sphereSobolevInclusionL 2 1 (by norm_num) u))=
      sphereSobolevInclusionL 0 (-1:ℝ) (by norm_num)
        (flatRaisingRotationCommutatorL i j a (sphereSobolevInclusionL 2 1 (by norm_num) u)+
          flatOneRaisingL a (sphereSobolevRotationL 2 i j u)) := by
  have hR : sphereSobolevRotationL ((1:ℝ)-1) i j=sphereSobolevRotationL 0 i j := by congr 1 <;> norm_num
  have hA : flatRaisingSobolevL ((1:ℝ)-1) a=flatRaisingSobolevL 0 a := by rw [show (1:ℝ)-1=0 by norm_num]
  have hI : sphereSobolevInclusionL ((1:ℝ)-1) (((1:ℝ)-1)-1) (by norm_num)=
      sphereSobolevInclusionL 0 (-1:ℝ) (by norm_num) := by congr 1 <;> norm_num
  have hComm := flatRaisingSobolevL_rotation_commutator 1 i j a
  rw [hR,hA,hI] at hComm
  have hPoint := DFunLike.congr_fun hComm (sphereSobolevInclusionL 2 1 (by norm_num) u)
  simp only [_root_.sub_apply,ContinuousLinearMap.comp_apply] at hPoint
  have hCompat := flatRaisingSobolevL_inclusion 1 0 (by norm_num) a
  have hI2 : sphereSobolevInclusionL ((1:ℝ)-1) ((0:ℝ)-1) (by norm_num)=
      sphereSobolevInclusionL 0 (-1:ℝ) (by norm_num) := by congr 1 <;> norm_num
  rw [hI2] at hCompat
  have hLow := DFunLike.congr_fun hCompat (sphereSobolevRotationL 2 i j u)
  simp only [ContinuousLinearMap.comp_apply] at hLow
  rw [sphereSobolevRotationL_one_inclusion_two,hLow] at hPoint
  rw [map_add]
  exact sub_eq_iff_eq_add.mp hPoint
end ShrinkingSpheres
