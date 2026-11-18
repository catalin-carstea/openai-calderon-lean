import Proof.SmoothFiniteJetBounds
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
open scoped ContDiff
namespace ShrinkingSpheres
namespace SmoothFiniteJetBound
variable {P E : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma sub {f g : P → E} {p : P} {N : ℕ} {B C : ℝ}
    (hf : SmoothFiniteJetBound f p N B) (hg : SmoothFiniteJetBound g p N C) :
    SmoothFiniteJetBound (fun x => f x-g x) p N (B+C) := by
  simpa only [neg_one_smul,abs_neg,abs_one,one_mul,sub_eq_add_neg] using hf.add (hg.const_smul (-1))

lemma linearCombination {κ : Type*} [Fintype κ] (q : κ → P → ℝ) (T : κ → E)
    (p : P) (N : ℕ) (B : ℝ) (hq : ∀ k,SmoothFiniteJetBound (q k) p N B) :
    SmoothFiniteJetBound (fun x => ∑ k,q k x • T k) p N ((∑ k,‖T k‖)*B) := by
  have hh := SmoothFiniteJetBound.sum (fun k x => q k x • T k) p N (fun k => ‖T k‖*B) (fun k => by
    let L : ℝ →L[ℝ] E := ContinuousLinearMap.toSpanSingleton ℝ (T k)
    have hL : ‖L‖=‖T k‖ := ContinuousLinearMap.norm_toSpanSingleton _
    have h := (hq k).clm L
    rw [hL] at h
    exact h)
  simpa only [← Finset.sum_mul] using hh
end SmoothFiniteJetBound
end ShrinkingSpheres
