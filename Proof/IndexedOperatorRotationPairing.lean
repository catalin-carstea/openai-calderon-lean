import Proof.RotationContractionAlgebra
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.FDeriv.CompCLM
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1400000
set_option maxSynthPendingDepth 30
namespace ShrinkingSpheres

lemma indexed_operator_rotation_pairing {D E F : Type*}
    [NormedAddCommGroup D] [NormedSpace ℝ D] [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (B : I → E →L[ℝ] F) (Q : I → D →L[ℝ] E) (i j : I) :
    (∑ k : I,((if k=j then B i else 0)-(if k=i then B j else 0)).comp (Q k)) =
      ∑ k : I,(B k).comp ((if k=i then Q j else 0)-(if k=j then Q i else 0)) := by
  have hIf (P : Prop) [Decidable P] (A : E →L[ℝ] F) (M : D →L[ℝ] E) :
      (if P then A else 0).comp M=(if P then A.comp M else 0) := by
    split_ifs <;> simp only [ContinuousLinearMap.zero_comp]
  simp only [ContinuousLinearMap.sub_comp,ContinuousLinearMap.comp_sub,hIf,clm_comp_ite_zero,
    Finset.sum_sub_distrib,Finset.sum_ite_eq',Finset.mem_univ,ite_true]

lemma hasDerivAt_sum_clm_comp {D E F κ : Type*}
    [NormedAddCommGroup D] [NormedSpace ℝ D] [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [Fintype κ]
    (A : κ → ℝ → E →L[ℝ] F) (dA : κ → E →L[ℝ] F)
    (B : κ → ℝ → D →L[ℝ] E) (dB : κ → D →L[ℝ] E) (t : ℝ)
    (hA : ∀ k,HasDerivAt (A k) (dA k) t) (hB : ∀ k,HasDerivAt (B k) (dB k) t) :
    HasDerivAt (fun s => ∑ k,(A k s).comp (B k s))
      (∑ k,((dA k).comp (B k t)+(A k t).comp (dB k))) t := by
  have hSum := HasDerivAt.sum (fun k (_ : k ∈ Finset.univ) => (hA k).clm_comp (hB k))
  have hFun : (∑ k,(fun s => (A k s).comp (B k s))) = (fun s => ∑ k,(A k s).comp (B k s)) := by
    funext s
    exact Finset.sum_apply _ _ _
  rw [hFun] at hSum
  exact hSum
end ShrinkingSpheres
