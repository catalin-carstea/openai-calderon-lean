import Proof.RelativeCoframeAngularCurve
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxSynthPendingDepth 30
namespace ShrinkingSpheres

lemma axis_sum_smul {E : Type*} [AddCommGroup E] [Module ℝ E] (F : I → E) (k : I) :
    (∑ l : I,(axis k) l • F l)=F k := by
  have hc (l : I) : (axis k) l = if l=k then 1 else 0 := by
    simp [axis,PiLp.single_apply,eq_comm]
  simp only [hc,ite_smul,one_smul,zero_smul,Finset.sum_ite_eq',Finset.mem_univ,ite_true]

lemma rotation_coefficients_sum {E : Type*} [AddCommGroup E] [Module ℝ E]
    (F dF : I → E) (i j k : I) :
    (∑ l : I,((rotationVectorL i j (axis k)) l • F l+(axis k) l • dF l)) =
      dF k+(if k=i then F j else 0)-(if k=j then F i else 0) := by
  rw [Finset.sum_add_distrib,axis_sum_smul]
  have hFirst : (∑ l : I,(rotationVectorL i j (axis k)) l • F l) =
      (if k=i then F j else 0)-(if k=j then F i else 0) := by
    rw [rotationVectorL_axis]
    split_ifs <;> simp only [PiLp.sub_apply,PiLp.zero_apply,sub_smul,
      Finset.sum_sub_distrib,axis_sum_smul,zero_smul,Finset.sum_const_zero]
  rw [hFirst]
  abel
end ShrinkingSpheres
