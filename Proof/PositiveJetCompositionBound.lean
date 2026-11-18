import Proof.FiniteJetBoundCalculus

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
open Set Filter
open scoped ContDiff Topology
namespace ShrinkingSpheres

lemma iteratedFDeriv_sub_const_pos
    {P E : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : P → E) (x : P) (hf : ContDiffAt ℝ ∞ f x) (c : E) (n : ℕ) (hn : 1 ≤ n) :
    iteratedFDeriv ℝ n (fun y => f y-c) x = iteratedFDeriv ℝ n f x := by
  change iteratedFDeriv ℝ n (f-(fun _ : P => c)) x = _
  rw [iteratedFDeriv_sub_apply (f:=f) (g:=fun _ : P => c) (hf.of_le (by simp)) (contDiffAt_const),
    iteratedFDeriv_const_of_ne (by omega),Pi.zero_apply,sub_zero]

/-- Positive output jets do not require a zeroth-order bound on the outer
    function. Translate its value to zero before applying the common budget. -/
theorem iteratedFDeriv_comp_positive_common_bound
    {P E F : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : P → E) (g : E → F) (x : P) (hf : ContDiffAt ℝ ∞ f x) (hg : ContDiffAt ℝ ∞ g (f x))
    (N : ℕ) (C D : ℝ) (hC : 0 ≤ C) (hD : 1 ≤ D)
    (hOuter : ∀ j : ℕ,1 ≤ j → j ≤ N → ‖iteratedFDeriv ℝ j g (f x)‖ ≤ C)
    (hInner : ∀ j : ℕ,1 ≤ j → j ≤ N → ‖iteratedFDeriv ℝ j f x‖ ≤ D)
    (n : ℕ) (hn : 1 ≤ n) (hnN : n ≤ N) :
    ‖iteratedFDeriv ℝ n (g ∘ f) x‖ ≤ (N.factorial:ℝ)*C*D^N := by
  let g0 : E → F := fun y => g y-g (f x)
  have hg0 : ContDiffAt ℝ ∞ g0 (f x) := hg.sub contDiffAt_const
  have hOuter0 (j : ℕ) (hj : j ≤ N) : ‖iteratedFDeriv ℝ j g0 (f x)‖ ≤ C := by
    by_cases hj0 : j = 0
    · subst j
      simpa only [norm_iteratedFDeriv_zero,g0,sub_self,norm_zero] using hC
    · change ‖iteratedFDeriv ℝ j (fun y => g y-g (f x)) (f x)‖ ≤ C
      rw [iteratedFDeriv_sub_const_pos g (f x) hg _ j (by omega)]
      exact hOuter j (by omega) hj
  have hh := iteratedFDeriv_comp_common_bound f g0 x hf hg0 N C D hC hD hOuter0 hInner n hnN
  change ‖iteratedFDeriv ℝ n (fun y => (g ∘ f) y-g (f x)) x‖ ≤ _ at hh
  rw [iteratedFDeriv_sub_const_pos (g ∘ f) x (hg.comp x hf) _ n hn] at hh
  exact hh

end ShrinkingSpheres
