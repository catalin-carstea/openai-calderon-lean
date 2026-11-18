import Proof.CoordinateHigherNorms
import Mathlib.Analysis.Calculus.ContDiff.Bounds

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 500000
open Set
open scoped ContDiff
namespace ShrinkingSpheres

lemma norm_iteratedFDeriv_mul_at {Ω : Set X} (hΩ : IsOpen Ω) {f g : X → ℝ}
    (hf : ContDiffOn ℝ ∞ f Ω) (hg : ContDiffOn ℝ ∞ g Ω) {y : X} (hy : y ∈ Ω) (n : ℕ) :
    ‖iteratedFDeriv ℝ n (fun x => f x*g x) y‖ ≤
      ∑ i ∈ Finset.range (n+1),(n.choose i : ℝ)*‖iteratedFDeriv ℝ i f y‖*
        ‖iteratedFDeriv ℝ (n-i) g y‖ := by
  have hb := norm_iteratedFDerivWithin_mul_le hf hg hΩ.uniqueDiffOn hy (n:=n) (by simp)
  have hEq (h : X → ℝ) (j : ℕ) : iteratedFDerivWithin ℝ j h Ω y = iteratedFDeriv ℝ j h y :=
    iteratedFDerivWithin_of_isOpen j hΩ hy
  simpa only [hEq] using hb

lemma norm_second_fderiv_mul_at {Ω : Set X} (hΩ : IsOpen Ω) {f g : X → ℝ}
    (hf : ContDiffOn ℝ ∞ f Ω) (hg : ContDiffOn ℝ ∞ g Ω) {y : X} (hy : y ∈ Ω) :
    ‖fderiv ℝ (fderiv ℝ (fun x => f x*g x)) y‖ ≤
      |f y| *‖fderiv ℝ (fderiv ℝ g) y‖+2*‖fderiv ℝ f y‖*‖fderiv ℝ g y‖+
        ‖fderiv ℝ (fderiv ℝ f) y‖*|g y| := by
  have hNorm (h : X → ℝ) : ‖iteratedFDeriv ℝ 2 h y‖ = ‖fderiv ℝ (fderiv ℝ h) y‖ := by
    rw [← norm_iteratedFDeriv_fderiv (n:=1),norm_iteratedFDeriv_one]
  have hb := norm_iteratedFDeriv_mul_at hΩ hf hg hy 2
  simpa only [Finset.sum_range_succ,Finset.sum_range_zero,Nat.choose_zero_right,
    Nat.choose_self,Nat.choose_one_right,Nat.cast_ofNat,Nat.cast_one,
    norm_iteratedFDeriv_zero,norm_iteratedFDeriv_one,hNorm,Real.norm_eq_abs,
    Nat.sub_zero,show (2:ℕ)-1=1 from rfl,show (2:ℕ)-2=0 from rfl,Nat.reduceSub,one_mul,zero_add] using hb

lemma norm_iteratedFDeriv_coordDeriv_le {Ω : Set X} (hΩ : IsOpen Ω) {f : X → ℝ}
    (hf : ContDiffOn ℝ ∞ f Ω) {y : X} (hy : y ∈ Ω) (i : I) (n : ℕ) :
    ‖iteratedFDeriv ℝ n (coordDeriv i f) y‖ ≤ ‖iteratedFDeriv ℝ (n+1) f y‖ := by
  have hD := ((hf.fderiv_of_isOpen (m:=∞) hΩ (by simp)).contDiffAt (hΩ.mem_nhds hy))
  have hb := norm_iteratedFDeriv_clm_apply_const (c:=axis i) hD (n:=n) (by simp)
  change ‖iteratedFDeriv ℝ n (fun x => fderiv ℝ f x (axis i)) y‖ ≤ _
  simpa only [norm_axis,one_mul,norm_iteratedFDeriv_fderiv] using hb

lemma norm_iteratedFDeriv_smul_const_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : X → ℝ} {y : X} (hf : ContDiffAt ℝ ∞ f y) (v : E) (n : ℕ) :
    ‖iteratedFDeriv ℝ n (fun x => f x • v) y‖ ≤ ‖v‖*‖iteratedFDeriv ℝ n f y‖ := by
  have hb := (ContinuousLinearMap.toSpanSingleton ℝ v).norm_iteratedFDeriv_comp_left hf (n:=n) (by simp)
  simpa only [Function.comp_def,ContinuousLinearMap.toSpanSingleton_apply,
    ContinuousLinearMap.norm_toSpanSingleton] using hb

end ShrinkingSpheres
