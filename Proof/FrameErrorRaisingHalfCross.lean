import Proof.BoundedCompositionCross
import Proof.FrameFirstAdjointEndpoints
import Proof.FlatRaisingHigherAlgebra
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
open Set
open scoped ContDiff Topology
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.SphereHarmonic

/-- The genuine raising map with its half-order codomain normalized. -/
def flatHalfRaisingL (i : I) :
    SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ)) := flatRaisingSobolevL (1/2:ℝ) i

/-- The SAME raising action on the higher balanced endpoint. -/
def flatThreeHalfRaisingL (i : I) :
    SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ) := flatRaisingSobolevL (3/2:ℝ) i

lemma norm_flatHalfRaisingL_le (i : I) :
    ‖flatHalfRaisingL i‖ ≤ 10*radialDriftSobolevBound (-(1/2:ℝ)) :=
  norm_flatRaisingSobolevL_le (1/2:ℝ) i

lemma norm_flatThreeHalfRaisingL_le (i : I) :
    ‖flatThreeHalfRaisingL i‖ ≤ 10*radialDriftSobolevBound (-(3/2:ℝ)) :=
  norm_flatRaisingSobolevL_le (3/2:ℝ) i

def flatZeroRaisingL (i : I) : SphereSobolev 0 →L[ℝ] SphereSobolev (-1:ℝ) := flatRaisingSobolevL 0 i

def flatTwoRaisingL (i : I) : SphereSobolev 2 →L[ℝ] SphereSobolev 1 := flatRaisingSobolevL 2 i

lemma flatHalfRaisingL_coarse (i : I) :
    (sphereSobolevInclusionL (-(1/2:ℝ)) (-1:ℝ) (by norm_num)).comp (flatHalfRaisingL i)=
      (flatZeroRaisingL i).comp (sphereSobolevInclusionL (1/2:ℝ) 0 (by norm_num)) := by
  have hh := (flatRaisingSobolevL_inclusion (1/2:ℝ) 0 (by norm_num) i).symm
  have hI : sphereSobolevInclusionL ((1/2:ℝ)-1) ((0:ℝ)-1) (by norm_num)=
      sphereSobolevInclusionL (-(1/2:ℝ)) (-1:ℝ) (by norm_num) := by congr 1 <;> norm_num
  rw [hI] at hh
  exact hh

lemma flatThreeHalfRaisingL_high (i : I) :
    (flatThreeHalfRaisingL i).comp (sphereSobolevInclusionL 2 (3/2:ℝ) (by norm_num))=
      (sphereSobolevInclusionL 1 (1/2:ℝ) (by norm_num)).comp (flatTwoRaisingL i) := by
  have hh := flatRaisingSobolevL_inclusion 2 (3/2:ℝ) (by norm_num) i
  have hI : sphereSobolevInclusionL ((2:ℝ)-1) ((3/2:ℝ)-1) (by norm_num)=
      sphereSobolevInclusionL 1 (1/2:ℝ) (by norm_num) := by congr 1 <;> norm_num
  rw [hI] at hh
  exact hh

/-- The E/raising cross terms use genuine half and higher endpoints of
    the SAME frame error, at the balanced H3/2-to-H(-1/2) orders. -/
def frameErrorRaisingHalfCrossL
    (L : I → X → SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ)))
    (H : I → X → SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ)) (x : X) :
    SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ)) :=
  ∑ i : I,((flatHalfRaisingL i).comp (H i x)+(L i x).comp (flatThreeHalfRaisingL i))

lemma norm_frameErrorRaisingHalfCrossL_le
    (L : I → X → SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ)))
    (H : I → X → SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ))
    (x : X) (q : ℝ) (hq : 0 ≤ q) (hL : ∀ i,‖L i x‖ ≤ q) (hH : ∀ i,‖H i x‖ ≤ q) :
    ‖frameErrorRaisingHalfCrossL L H x‖ ≤
      3*(10*radialDriftSobolevBound (-(1/2:ℝ))+10*radialDriftSobolevBound (-(3/2:ℝ)))*q := by
  have hEach (i : I) : ‖(flatHalfRaisingL i).comp (H i x)+(L i x).comp (flatThreeHalfRaisingL i)‖ ≤
      (10*radialDriftSobolevBound (-(1/2:ℝ))+10*radialDriftSobolevBound (-(3/2:ℝ)))*q :=
    norm_bounded_composition_cross_le _ _ _ _
      (mul_nonneg (by norm_num) (zero_le_one.trans (le_max_left _ _))) hq
      (norm_flatHalfRaisingL_le i) (norm_flatThreeHalfRaisingL_le i) (hL i) (hH i)

  calc
    _ ≤ ∑ i : I,‖(flatHalfRaisingL i).comp (H i x)+(L i x).comp (flatThreeHalfRaisingL i)‖ := norm_sum_le _ _
    _ ≤ ∑ _i : I,(10*radialDriftSobolevBound (-(1/2:ℝ))+10*radialDriftSobolevBound (-(3/2:ℝ)))*q :=
      Finset.sum_le_sum (fun i _ => hEach i)
    _ = _ := by simp only [Fin.sum_univ_three];ring

lemma contDiffOn_frameErrorRaisingHalfCrossL {Y : Set X}
    (L : I → X → SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ)))
    (H : I → X → SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ))
    (hL : ∀ i,ContDiffOn ℝ ∞ (L i) Y) (hH : ∀ i,ContDiffOn ℝ ∞ (H i) Y) :
    ContDiffOn ℝ ∞ (frameErrorRaisingHalfCrossL L H) Y := by
  apply ContDiffOn.sum
  intro i _
  exact (contDiffOn_const.clm_comp (hH i)).add ((hL i).clm_comp contDiffOn_const)
end ShrinkingSpheres
