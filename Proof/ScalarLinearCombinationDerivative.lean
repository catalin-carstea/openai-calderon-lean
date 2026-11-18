import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxSynthPendingDepth 30
open scoped ContDiff
namespace ShrinkingSpheres

lemma hasDerivAt_sum_smul_family {E κ : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [Fintype κ]
    (q : κ → ℝ → ℝ) (dq : κ → ℝ) (F : κ → ℝ → E) (dF : κ → E) (t : ℝ)
    (hq : ∀ k,HasDerivAt (q k) (dq k) t) (hF : ∀ k,HasDerivAt (F k) (dF k) t) :
    HasDerivAt (fun s => ∑ k,q k s • F k s) (∑ k,(dq k • F k t+q k t • dF k)) t := by
  have hSum := HasDerivAt.sum (fun k (_ : k ∈ Finset.univ) => (hq k).smul (hF k))
  have hFun : (∑ k,q k • F k)=(fun s => ∑ k,q k s • F k s) := by
    funext s
    simp only [Finset.sum_apply]
    exact Finset.sum_congr rfl (fun k _ => rfl)
  rw [hFun] at hSum
  simpa only [add_comm] using hSum

lemma hasDerivAt_scalar_linearCombination {E κ : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [Fintype κ] (q : κ → ℝ → ℝ) (dq : κ → ℝ) (T : κ → E) (t : ℝ)
    (hq : ∀ k,HasDerivAt (q k) (dq k) t) :
    HasDerivAt (fun s => ∑ k,q k s • T k) (∑ k,dq k • T k) t := by
  simpa only [smul_zero,add_zero] using hasDerivAt_sum_smul_family q dq (fun k _ => T k) (fun _ => 0) t
    hq (fun k => hasDerivAt_const t (T k))
end ShrinkingSpheres
