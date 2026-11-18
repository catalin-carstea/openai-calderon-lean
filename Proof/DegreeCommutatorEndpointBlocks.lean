import Proof.RotationGraphHarmonicBlocks
import Proof.Archive.SphereSobolevShiftedPhysicalDegree

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2600000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set
open scoped ContDiff Topology InnerProductSpace ENNReal
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.SphereHarmonic

def degreeEndpointCommutator
    (Hi : SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ))
    (Lo : SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ))) :
    SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ)) :=
  (sphereSobolevShiftedDegreeL (1/2:ℝ)).comp Hi-Lo.comp (sphereSobolevShiftedDegreeL (3/2:ℝ))

/-- Compatible genuine low/high/midpoint response witnesses give the exact
    physical degree-commutator block, with no norm assumptions on a cutoff. -/
theorem degreeEndpointCommutator_physical_block
    (Hi : SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ))
    (Lo : SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ)))
    (R : SphereSobolev 1 →L[ℝ] SphereSobolev 0)
    (hMid : (sphereSobolevInclusionL (1/2:ℝ) 0 (by norm_num)).comp Hi =
      R.comp (sphereSobolevInclusionL (3/2:ℝ) 1 (by norm_num)))
    (hLow : (sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)).comp Hi =
      Lo.comp (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)))
    (m n : ℕ) (z : harmonicSphereSubspace n) :
    sphereSobolevCoefficientL (-(1/2:ℝ)) m
      (degreeEndpointCommutator Hi Lo (sphereSobolevSingleL (3/2:ℝ) n z)) =
        ((m:ℝ)-(n:ℝ)) • coarsePhysicalHarmonicBlock R m n z := by
  let u := sphereSobolevSingleL (3/2:ℝ) n z
  have hMidPoint := congrArg (fun T : SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev 0 =>
    sphereSobolevCoefficientL 0 m (T u)) hMid
  dsimp only [u] at hMidPoint
  simp only [ContinuousLinearMap.comp_apply,sphereSobolevCoefficientL_inclusion,
    sphereSobolevInclusionL_single] at hMidPoint
  have hLowPoint := congrArg (fun T : SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ)) =>
    sphereSobolevCoefficientL (-(1/2:ℝ)) m (T u)) hLow
  dsimp only [u] at hLowPoint
  simp only [ContinuousLinearMap.comp_apply,sphereSobolevCoefficientL_inclusion,
    sphereSobolevInclusionL_single] at hLowPoint
  have hDegree : sphereSobolevCoefficientL (-(1/2:ℝ)) m
      (sphereSobolevShiftedDegreeL (1/2:ℝ) (Hi u)) =
      (m:ℝ) • sphereSobolevCoefficientL (1/2:ℝ) m (Hi u) := by
    simpa only [sphereSobolevCoefficientL,show (1/2:ℝ)-1=-(1/2:ℝ) by norm_num] using
      sphereSobolevCoefficientL_shiftedDegree (1/2:ℝ) m (Hi u)
  have hSingle : sphereSobolevShiftedDegreeL (3/2:ℝ) u =
      (n:ℝ) • sphereSobolevSingleL (1/2:ℝ) n z := by
    simpa only [u,sphereSobolevSingleL,show (3/2:ℝ)-1=(1/2:ℝ) by norm_num] using
      sphereSobolevShiftedDegreeL_single (3/2:ℝ) n z
  change sphereSobolevCoefficientL (-(1/2:ℝ)) m
    ((sphereSobolevShiftedDegreeL (1/2:ℝ)) (Hi u)-Lo (sphereSobolevShiftedDegreeL (3/2:ℝ) u)) = _
  rw [map_sub,hDegree,hSingle,map_smul,map_smul]
  rw [← hLowPoint,hMidPoint]
  change (m:ℝ) • coarsePhysicalHarmonicBlock R m n z-(n:ℝ) • coarsePhysicalHarmonicBlock R m n z = _
  exact (sub_smul _ _ _).symm

end ShrinkingSpheres
