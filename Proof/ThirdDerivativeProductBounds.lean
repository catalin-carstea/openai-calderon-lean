import Proof.LocalHigherDerivativeBounds

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 700000
set_option maxSynthPendingDepth 15
open Set
open scoped ContDiff
namespace ShrinkingSpheres

lemma norm_iteratedFDeriv_two_eq_nested {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : X → E) (y : X) : ‖iteratedFDeriv ℝ 2 f y‖ = ‖fderiv ℝ (fderiv ℝ f) y‖ := by
  rw [← norm_iteratedFDeriv_fderiv (n:=1),norm_iteratedFDeriv_one]

lemma norm_iteratedFDeriv_three_eq_nested {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : X → E) (y : X) : ‖iteratedFDeriv ℝ 3 f y‖ = ‖fderiv ℝ (fderiv ℝ (fderiv ℝ f)) y‖ := by
  rw [← norm_iteratedFDeriv_fderiv (n:=2),norm_iteratedFDeriv_two_eq_nested]

lemma norm_iteratedFDeriv_smul_at {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {Ω : Set X} (hΩ : IsOpen Ω) {f : X → ℝ} {g : X → E}
    (hf : ContDiffOn ℝ ∞ f Ω) (hg : ContDiffOn ℝ ∞ g Ω) {y : X} (hy : y ∈ Ω) (n : ℕ) :
    ‖iteratedFDeriv ℝ n (fun x => f x • g x) y‖ ≤
      ∑ i ∈ Finset.range (n+1),(n.choose i : ℝ)*‖iteratedFDeriv ℝ i f y‖*
        ‖iteratedFDeriv ℝ (n-i) g y‖ := by
  have hb := norm_iteratedFDerivWithin_smul_le hf hg hΩ.uniqueDiffOn hy (n:=n) (by simp)
  have hEqScalar (q : X → ℝ) (j : ℕ) :
      iteratedFDerivWithin ℝ j q Ω y = iteratedFDeriv ℝ j q y :=
    iteratedFDerivWithin_of_isOpen j hΩ hy
  have hEqVector (q : X → E) (j : ℕ) :
      iteratedFDerivWithin ℝ j q Ω y = iteratedFDeriv ℝ j q y :=
    iteratedFDerivWithin_of_isOpen j hΩ hy
  simpa only [hEqScalar,hEqVector] using hb

lemma norm_second_fderiv_smul_at {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {Ω : Set X} (hΩ : IsOpen Ω) {f : X → ℝ} {g : X → E}
    (hf : ContDiffOn ℝ ∞ f Ω) (hg : ContDiffOn ℝ ∞ g Ω) {y : X} (hy : y ∈ Ω) :
    ‖fderiv ℝ (fderiv ℝ (fun x => f x • g x)) y‖ ≤
      |f y| * ‖fderiv ℝ (fderiv ℝ g) y‖ + 2*‖fderiv ℝ f y‖*‖fderiv ℝ g y‖ +
        ‖fderiv ℝ (fderiv ℝ f) y‖*‖g y‖ := by
  have hb := norm_iteratedFDeriv_smul_at hΩ hf hg hy 2
  simpa only [Finset.sum_range_succ,Finset.sum_range_zero,Nat.choose_zero_right,
    Nat.choose_self,Nat.choose_one_right,Nat.cast_ofNat,Nat.cast_one,
    norm_iteratedFDeriv_zero,norm_iteratedFDeriv_one,norm_iteratedFDeriv_two_eq_nested,
    Real.norm_eq_abs,Nat.sub_zero,show (2:ℕ)-1=1 from rfl,
    show (2:ℕ)-2=0 from rfl,Nat.reduceSub,one_mul,zero_add] using hb

lemma norm_third_fderiv_mul_at {Ω : Set X} (hΩ : IsOpen Ω) {f g : X → ℝ}
    (hf : ContDiffOn ℝ ∞ f Ω) (hg : ContDiffOn ℝ ∞ g Ω) {y : X} (hy : y ∈ Ω) :
    ‖fderiv ℝ (fderiv ℝ (fderiv ℝ (fun x => f x*g x))) y‖ ≤
      |f y| * ‖fderiv ℝ (fderiv ℝ (fderiv ℝ g)) y‖ +
      3*‖fderiv ℝ f y‖*‖fderiv ℝ (fderiv ℝ g) y‖ +
      3*‖fderiv ℝ (fderiv ℝ f) y‖*‖fderiv ℝ g y‖ +
      ‖fderiv ℝ (fderiv ℝ (fderiv ℝ f)) y‖*|g y| := by
  have hb := norm_iteratedFDeriv_mul_at hΩ hf hg hy 3
  simpa only [Finset.sum_range_succ,Finset.sum_range_zero,Nat.choose_zero_right,
    Nat.choose_self,Nat.choose_one_right,show (3:ℕ).choose 2=3 from rfl,
    Nat.cast_ofNat,Nat.cast_one,norm_iteratedFDeriv_zero,norm_iteratedFDeriv_one,
    norm_iteratedFDeriv_two_eq_nested,norm_iteratedFDeriv_three_eq_nested,
    Real.norm_eq_abs,Nat.sub_zero,show (3:ℕ)-1=2 from rfl,
    show (3:ℕ)-2=1 from rfl,show (3:ℕ)-3=0 from rfl,Nat.reduceSub,
    one_mul,zero_add] using hb

lemma norm_iteratedFDeriv_finite_sum_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {ι : Type*} (s : Finset ι) (F : ι → X → E) (y : X) (n : ℕ)
    (hF : ∀ i ∈ s, ContDiffAt ℝ ∞ (F i) y) :
    ‖iteratedFDeriv ℝ n (fun x => ∑ i ∈ s,F i x) y‖ ≤
      ∑ i ∈ s,‖iteratedFDeriv ℝ n (F i) y‖ := by
  rw [iteratedFDeriv_fun_sum_apply (fun i hi => (hF i hi).of_le (by simp))]
  exact norm_sum_le _ _

end ShrinkingSpheres
