import Proof.RotationCommutatorHighLift
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxSynthPendingDepth 30
set_option maxRecDepth 2400
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
open scoped InnerProductSpace
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.SphereHarmonic

abbrev RotationHighLiftData :=
  (SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ))) ×
    (I × I → SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ)))

/-- The supplied reconstruction is a fixed continuous linear operation on
one low operator and its nine SAME rotation commutators. -/
def rotationHighLiftDataL : RotationHighLiftData →L[ℝ]
    (SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ)) :=
  let low := SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ))
  let I1 := sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)
  let F : RotationHighLiftData →L[ℝ] low := ContinuousLinearMap.fst ℝ _ _
  let D (ij : I × I) : RotationHighLiftData →L[ℝ] low :=
    (ContinuousLinearMap.proj ij).comp (ContinuousLinearMap.snd ℝ _ _)
  let Pre (U : SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ)) :
      low →L[ℝ] (SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ))) :=
    (ContinuousLinearMap.compL ℝ (SphereSobolev (3/2:ℝ)) (SphereSobolev (1/2:ℝ)) (SphereSobolev (-(1/2:ℝ)))).flip U
  let Out (U : SphereSobolev (-(1/2:ℝ)) →L[ℝ] SphereSobolev (1/2:ℝ)) :=
    ContinuousLinearMap.compL ℝ (SphereSobolev (3/2:ℝ)) (SphereSobolev (-(1/2:ℝ))) (SphereSobolev (1/2:ℝ)) U
  (Out sphereSobolevTraceReconstructionIdentityL).comp ((Pre I1).comp F)+
    ∑ ij : I × I,(Out (sphereSobolevTraceReconstructionRotationL ij.1 ij.2)).comp
      ((Pre (sphereSobolevRotationL (3/2:ℝ) ij.1 ij.2)).comp F+(Pre I1).comp (D ij))

lemma rotationHighLiftDataL_apply (x : RotationHighLiftData) :
    rotationHighLiftDataL x=sphereSobolevRotationCommutatorHighLiftL x.1 (fun i j => x.2 (i,j)) := by
  apply ContinuousLinearMap.ext
  intro u
  simp only [rotationHighLiftDataL,sphereSobolevRotationCommutatorHighLiftL,
    ContinuousLinearMap.comp_apply,_root_.add_apply,_root_.sum_apply,ContinuousLinearMap.compL_apply,
    ContinuousLinearMap.flip_apply,
    ContinuousLinearMap.proj_apply]
  rw [Fintype.sum_prod_type]
  rfl

lemma norm_rotationHighLiftDataL_le : ‖rotationHighLiftDataL‖ ≤ 19+9*Real.sqrt 2 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro x
  rw [rotationHighLiftDataL_apply]
  have hSum : (∑ i : I,∑ j : I,‖x.2 (i,j)‖) ≤ 9*‖x‖ := by
    have hEach (i j : I) : ‖x.2 (i,j)‖ ≤ ‖x‖ := (norm_le_pi_norm x.2 (i,j)).trans (norm_snd_le x)
    exact (Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ => hEach i j))).trans_eq (by simp [Fin.sum_univ_three];ring)
  exact (norm_sphereSobolevRotationCommutatorHighLiftL_le _ _).trans
    ((add_le_add (mul_le_mul_of_nonneg_left (norm_fst_le x) (by norm_num))
      (mul_le_mul_of_nonneg_left hSum (Real.sqrt_nonneg 2))).trans_eq (by ring))
end ShrinkingSpheres
