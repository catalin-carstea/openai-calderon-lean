import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Tactic.Module
import Mathlib.Tactic.Linarith
noncomputable section
set_option autoImplicit false
namespace ShrinkingSpheres
variable {E F H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup H] [NormedSpace ℝ H]

def halfScalarCommutatorCorrectionL (G K Mh : H →L[ℝ] H) : H →L[ℝ] H :=
  G+K.comp Mh-Mh.comp K

/-- A common order-zero antisymmetric difference transports the forward
scalar commutator to the SAME adjoint operator at the positive-half endpoint. -/
lemma half_scalar_commutator_of_difference
    (I : E →L[ℝ] H) (J : H →L[ℝ] F) (P Pa : E →L[ℝ] F)
    (G K Mh : H →L[ℝ] H) (M1 : E →L[ℝ] E) (M0 : F →L[ℝ] F)
    (hG : J.comp (G.comp I)=P.comp M1-M0.comp P)
    (hK : J.comp (K.comp I)=Pa-P)
    (hM1 : Mh.comp I=I.comp M1) (hM0 : J.comp Mh=M0.comp J) :
    J.comp ((halfScalarCommutatorCorrectionL G K Mh).comp I)=Pa.comp M1-M0.comp Pa := by
  apply ContinuousLinearMap.ext
  intro u
  have hg := DFunLike.congr_fun hG u
  have hk (v : E) : J (K (I v))=Pa v-P v := DFunLike.congr_fun hK v
  have hm1 := DFunLike.congr_fun hM1 u
  have hm0 := DFunLike.congr_fun hM0 (K (I u))
  change J (G (I u))=P (M1 u)-M0 (P u) at hg
  change Mh (I u)=I (M1 u) at hm1
  change J (Mh (K (I u)))=M0 (J (K (I u))) at hm0
  change J ((G+K.comp Mh-Mh.comp K) (I u))=Pa (M1 u)-M0 (Pa u)
  simp only [_root_.sub_apply,_root_.add_apply,ContinuousLinearMap.comp_apply,map_sub,map_add]
  rw [hg,hm1,hm0,hk (M1 u),hk u,map_sub]
  module

lemma norm_halfScalarCommutatorCorrectionL_le (G K Mh : H →L[ℝ] H) :
    ‖halfScalarCommutatorCorrectionL G K Mh‖ ≤ ‖G‖+2*‖K‖*‖Mh‖ := by
  change ‖G+K.comp Mh-Mh.comp K‖ ≤ _
  have hSub := norm_sub_le (G+K.comp Mh) (Mh.comp K)
  have hAdd := norm_add_le G (K.comp Mh)
  have hOne := ContinuousLinearMap.opNorm_comp_le K Mh
  have hTwo := ContinuousLinearMap.opNorm_comp_le Mh K
  nlinarith only [hSub,hAdd,hOne,hTwo]
end ShrinkingSpheres
