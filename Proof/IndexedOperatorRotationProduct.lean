import Proof.IndexedOperatorRotationPairing
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
namespace ShrinkingSpheres
lemma indexed_rotation_product_rule {D E F : Type*}
    [NormedAddCommGroup D] [NormedSpace ℝ D] [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (B : I → E →L[ℝ] F) (Q dQ : I → D →L[ℝ] E)
    (A : E →L[ℝ] F) (M : I → E →L[ℝ] E) (i j : I) :
    (∑ k : I,((((if k=j then B i else 0)-(if k=i then B j else 0))+A.comp (M k)).comp (Q k)+
      (B k).comp (dQ k))) =
      (∑ k : I,(B k).comp ((dQ k)+(if k=i then Q j else 0)-(if k=j then Q i else 0)))+
        A.comp (∑ k : I,(M k).comp (Q k)) := by
  have hPair := indexed_operator_rotation_pairing B Q i j
  have hSum : (∑ k : I,A.comp ((M k).comp (Q k)))=A.comp (∑ k : I,(M k).comp (Q k)) := by
    apply ContinuousLinearMap.ext
    intro u
    simp only [_root_.sum_apply,ContinuousLinearMap.comp_apply,map_sum]
  have hEach (k : I) : (B k).comp ((dQ k)+(if k=i then Q j else 0)-(if k=j then Q i else 0)) =
      (B k).comp (dQ k)+(B k).comp ((if k=i then Q j else 0)-(if k=j then Q i else 0)) := by
    simp only [ContinuousLinearMap.comp_sub,ContinuousLinearMap.comp_add]
    abel
  simp only [ContinuousLinearMap.add_comp,ContinuousLinearMap.comp_assoc,Finset.sum_add_distrib,hEach]
  rw [hPair,hSum]
  abel
end ShrinkingSpheres
