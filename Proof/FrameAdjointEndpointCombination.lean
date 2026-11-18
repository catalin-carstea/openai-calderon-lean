import Proof.LowBoundedCorrectionAdjoint
import Proof.ActualFrameErrorEndpointPair
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped InnerProductSpace
namespace ShrinkingSpheres

lemma finite_real_adjoint_balanced_combination {E H κ : Type*} [Fintype κ]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup H] [NormedSpace ℝ H]
    (I0 : E →L[ℝ] E) (I1 : H →L[ℝ] E) (L : κ → E →L[ℝ] E) (A : κ → H →L[ℝ] E)
    (hA : ∀ a,I0.comp (A a)=(L a).adjoint.comp I1) (u : κ → ℝ) :
    I0.comp (∑ a,u a • A a)=(∑ a,u a • L a).adjoint.comp I1 := by
  have hAdj : (∑ a,u a • L a).adjoint=∑ a,u a • (L a).adjoint := by
    simp only [map_sum,map_smul]
  rw [hAdj]
  apply ContinuousLinearMap.ext
  intro x
  simp only [ContinuousLinearMap.comp_apply,_root_.sum_apply,_root_.smul_apply,map_sum,map_smul]
  exact Finset.sum_congr rfl (fun a _ => congrArg (fun z => u a • z) (DFunLike.congr_fun (hA a) x))
end ShrinkingSpheres
