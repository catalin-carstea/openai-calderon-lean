import Proof.Geometry
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
namespace ShrinkingSpheres
lemma clm_ite_zero_apply {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (P : Prop) [Decidable P] (A : E →L[ℝ] F) (u : E) :
    (if P then A else 0) u=(if P then A u else 0) := by
  split_ifs <;> rfl

lemma clm_apply_ite_zero {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (P : Prop) [Decidable P] (A : E →L[ℝ] F) (u : E) :
    A (if P then u else 0)=(if P then A u else 0) := by
  split_ifs <;> simp only [map_zero]

lemma clm_comp_ite_zero {D E F : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    (P : Prop) [Decidable P] (A : E →L[ℝ] F) (B : D →L[ℝ] E) :
    A.comp (if P then B else 0)=(if P then A.comp B else 0) := by
  split_ifs <;> simp only [ContinuousLinearMap.comp_zero]

lemma rotation_coordinate_contraction {F : Type*} [AddCommGroup F]
    (v : I → I → I → F) (i j k : I) :
    -(∑ a : I,((if j=a then v i k a else 0)-(if j=k then v i a a else 0)-
      (if i=a then v j k a else 0)+(if i=k then v j a a else 0)+
      (if a=j then v a k i else 0)-(if a=i then v a k j else 0))) =
      (if k=j then ∑ a : I,v i a a else 0)-(if k=i then ∑ a : I,v j a a else 0) := by
  classical
  have hIf (P : Prop) [Decidable P] (f : I → F) :
      (∑ a : I,if P then f a else 0)=(if P then ∑ a : I,f a else 0) := by
    split_ifs <;> simp only [Finset.sum_const_zero]
  simp only [Finset.sum_add_distrib,Finset.sum_sub_distrib,
    Finset.sum_ite_eq,Finset.sum_ite_eq',Finset.mem_univ,ite_true,hIf]
  simp only [eq_comm]
  abel

lemma sum_skew_contraction {F : Type*} [AddCommGroup F]
    (v : I → I → I → F) (hSkew : ∀ i j a,v i j a = -v j i a) (i : I) :
    (∑ a : I,v i a a) = -(∑ a : I,v a i a) := by
  calc
    _ = ∑ a : I,-v a i a := Finset.sum_congr rfl (fun a _ => hSkew i a a)
    _ = _ := by rw [Finset.sum_neg_distrib]
end ShrinkingSpheres
