import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Tactic.Abel
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace ShrinkingSpheres
lemma operator_commutator_sub_id {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (B M : E →L[ℝ] E) :
    B.comp (M-ContinuousLinearMap.id ℝ E)-(M-ContinuousLinearMap.id ℝ E).comp B=B.comp M-M.comp B := by
  simp only [ContinuousLinearMap.comp_sub,ContinuousLinearMap.sub_comp,ContinuousLinearMap.comp_id,ContinuousLinearMap.id_comp]
  abel
lemma scalar_expansion_algebra {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (K C C1 CR B M : E →L[ℝ] E) (r : ℝ) (hC : C=r • C1+CR) :
    -K+C+r • (B.comp M-M.comp B)=r • C1+
      (-K+CR+r • (B.comp (M-ContinuousLinearMap.id ℝ E)-(M-ContinuousLinearMap.id ℝ E).comp B)) := by
  rw [hC,operator_commutator_sub_id]
  abel
end ShrinkingSpheres
