import Proof.FiniteJetCompositionBound

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
open Set Filter
open scoped ContDiff Topology
namespace ShrinkingSpheres

theorem norm_iteratedFDeriv_clm_comp_le
    {P E F : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    (L : E →L[ℝ] F) (f : P → E) (x : P) (hf : ContDiffAt ℝ ∞ f x) (n : ℕ) :
    ‖iteratedFDeriv ℝ n (L ∘ f) x‖ ≤ ‖L‖*‖iteratedFDeriv ℝ n f x‖ := by
  rw [L.iteratedFDeriv_comp_left hf (i:=n) (by simp)]
  apply ContinuousMultilinearMap.opNorm_le_bound (mul_nonneg (norm_nonneg _) (norm_nonneg _))
  intro m
  change ‖L (iteratedFDeriv ℝ n f x m)‖ ≤ _
  exact (L.le_opNorm _).trans ((mul_le_mul_of_nonneg_left
    ((iteratedFDeriv ℝ n f x).le_opNorm m) (norm_nonneg L)).trans_eq (by ring))

/-- A single common budget for all derivatives through a finite order after
    composition, using positive input jets only. -/
theorem iteratedFDeriv_comp_common_bound
    {P E F : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : P → E) (g : E → F) (x : P) (hf : ContDiffAt ℝ ∞ f x) (hg : ContDiffAt ℝ ∞ g (f x))
    (N : ℕ) (C D : ℝ) (hC : 0 ≤ C) (hD : 1 ≤ D)
    (hOuter : ∀ j : ℕ,j ≤ N → ‖iteratedFDeriv ℝ j g (f x)‖ ≤ C)
    (hInner : ∀ j : ℕ,1 ≤ j → j ≤ N → ‖iteratedFDeriv ℝ j f x‖ ≤ D)
    (n : ℕ) (hn : n ≤ N) :
    ‖iteratedFDeriv ℝ n (g ∘ f) x‖ ≤ (N.factorial:ℝ)*C*D^N := by
  have hh := norm_iteratedFDeriv_comp_at_bound f g x hf hg n C D
    (fun j hj => hOuter j (hj.trans hn))
    (fun j hj hjn => (hInner j hj (hjn.trans hn)).trans (le_self_pow₀ hD (by omega)))
  have hFac : (n.factorial:ℝ) ≤ (N.factorial:ℝ) := by exact_mod_cast Nat.factorial_le hn
  have hPow : D^n ≤ D^N := pow_le_pow_right₀ hD hn
  apply hh.trans
  gcongr

end ShrinkingSpheres
