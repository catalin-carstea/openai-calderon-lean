import Proof.ParallelModelFirstModelHalf
import Proof.ParallelFirstSelfCoreSplit

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2800000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
open scoped InnerProductSpace
namespace ShrinkingSpheres.ParallelEnergy
open OAI.AnisotropicCalderon.SphereHarmonic

/-- Exact two-base / zero-base / complete-adjoint-defect split over an
abstract real Hilbert carrier. It does not choose any endpoint witness. -/
lemma model_first_core_pair_split {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    (g : I → I → ℝ) (ell : I → ℝ) (R A Z Y : I → I → F) (B T : I → F) (δ : F) :
    ⟪∑ k : I,∑ c : I,g k c • (R k c+ell k • Z k c),∑ b : I,B b⟫_ℝ-
      ⟪∑ k : I,∑ c : I,g k c • (-A k c+ell k • Y k c),-(∑ b : I,T b)+δ⟫_ℝ=
    (∑ k : I,∑ c : I,∑ b : I,g k c*(⟪R k c,B b⟫_ℝ-⟪A k c,T b⟫_ℝ))+
      (∑ k : I,∑ c : I,∑ b : I,(g k c*ell k)*(⟪Z k c,B b⟫_ℝ+⟪Y k c,T b⟫_ℝ))-
      ⟪∑ k : I,∑ c : I,g k c • (-A k c+ell k • Y k c),δ⟫_ℝ := by
  rw [inner_add_right,sub_add_eq_sub_sub]
  apply congrArg (fun t : ℝ => t-⟪∑ k : I,∑ c : I,g k c • (-A k c+ell k • Y k c),δ⟫_ℝ)
  simp only [sum_inner]
  simp only [real_inner_smul_left,inner_add_left,inner_neg_left,inner_neg_right,inner_sum,
    Finset.mul_sum]
  simp only [←Finset.sum_sub_distrib,←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro c _
  rw [sub_neg_eq_add,←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro b _
  ring

lemma model_first_coarse_high_pair_of_graph
    (C : SphereSobolev 1 →L[ℝ] SphereSobolev 0)
    (L : SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ)))
    (H : SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ))
    (hC : (sphereSobolevInclusionL 0 (-(1/2:ℝ)) (by norm_num)).comp C=
      L.comp (sphereSobolevInclusionL 1 (1/2:ℝ) (by norm_num)))
    (hH : (sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)).comp H=
      L.comp (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num))) (u : SphereSobolev (3/2:ℝ)) :
    sphereSobolevInclusionL (1/2:ℝ) 0 (by norm_num) (H u)=
      C (sphereSobolevInclusionL (3/2:ℝ) 1 (by norm_num) u) := by
  apply sphereSobolevInclusionL_injective 0 (-(1/2:ℝ)) (by norm_num)
  have h := DFunLike.congr_fun hC (sphereSobolevInclusionL (3/2:ℝ) 1 (by norm_num) u)
  have ht := DFunLike.congr_fun hH u
  simp only [ContinuousLinearMap.comp_apply,sphereSobolevInclusionL_trans_apply] at h ht ⊢
  exact ht.trans h.symm

end ShrinkingSpheres.ParallelEnergy
