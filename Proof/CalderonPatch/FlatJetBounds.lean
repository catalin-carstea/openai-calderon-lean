module

public import Mathlib.Analysis.Calculus.ContDiff.Bounds

import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Tactic.Linarith

@[expose] public section

noncomputable section
open Filter Metric Set
open scoped ContDiff Topology

namespace CalderonPatch

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- If the derivatives through order `m` vanish at a point, each
derivative of order `j ≤ m+1` on a small ball is bounded by its radius
to the power `m+1-j`. This estimate will control a shrinking cutoff
around the support of a point distribution. -/
theorem exists_flatJet_bound {f : E → F} (hf : ContDiff ℝ ∞ f)
    (p : E) (m : ℕ) (hZero : ∀ j ≤ m, iteratedFDeriv ℝ j f p = 0) :
    ∃ r > 0, ∃ C > 0, ∀ δ : ℝ, 0 < δ → δ ≤ r →
      ∀ x ∈ closedBall p δ, ∀ j ≤ m + 1, ‖iteratedFDeriv ℝ j f x‖ ≤ C * δ ^ (m + 1 - j) := by
  let C := ‖iteratedFDeriv ℝ (m + 1) f p‖ + 1
  have hC : 0 < C := by positivity
  have hCont : ContinuousAt (fun x => ‖iteratedFDeriv ℝ (m + 1) f x‖) p :=
    (hf.continuous_iteratedFDeriv (by simp : (m + 1 : ℕ) ≤ (∞ : ℕ∞ω))).norm.continuousAt
  have hSmall : ∀ᶠ x in 𝓝 p, ‖iteratedFDeriv ℝ (m + 1) f x‖ < C :=
    hCont.eventually_lt continuousAt_const (lt_add_one _)
  obtain ⟨ρ, hρ, hρsub⟩ := Metric.mem_nhds_iff.mp hSmall
  let r := ρ / 2
  have hr : 0 < r := by positivity
  have hrρ : r < ρ := by dsimp [r]; linarith
  refine ⟨r, hr, C, hC, ?_⟩
  intro δ hδ hδr
  have hBall : closedBall p δ ⊆ ball p ρ := closedBall_subset_ball (hδr.trans_lt hrρ)
  have hI : ∀ k ≤ m + 1, ∀ x ∈ closedBall p δ,
      ‖iteratedFDeriv ℝ (m + 1 - k) f x‖ ≤ C * δ ^ k := by
    intro k
    induction k with
    | zero =>
      intro _ x hx
      simpa only [Nat.sub_zero, pow_zero, mul_one] using (hρsub (hBall hx)).le
    | succ k ih =>
      intro hk x hx
      let j := m + 1 - (k + 1)
      have hj : j ≤ m := by dsimp [j]; omega
      have hnext : j + 1 = m + 1 - k := by dsimp [j]; omega
      have hfd : Differentiable ℝ (iteratedFDeriv ℝ j f) :=
        hf.differentiable_iteratedFDeriv
          (show (j : ℕ∞ω) < ∞ by exact_mod_cast ENat.natCast_lt_top j)
      have hd (y : E) (hy : y ∈ closedBall p δ) :
          ‖fderiv ℝ (iteratedFDeriv ℝ j f) y‖ ≤ C * δ ^ k := by
        rw [fderiv_iteratedFDeriv, Function.comp_apply, LinearIsometryEquiv.norm_map]
        exact (congrArg (fun k : ℕ => ‖iteratedFDeriv ℝ k f y‖) hnext).le.trans (ih (by omega) y hy)
      have hMean := (convex_closedBall p δ).norm_image_sub_le_of_norm_hasFDerivWithin_le
        (fun y _ => (hfd y).hasFDerivAt.hasFDerivWithinAt) hd (mem_closedBall_self hδ.le) hx
      rw [hZero j hj, sub_zero] at hMean
      calc
        _ ≤ (C * δ ^ k) * ‖x - p‖ := hMean
        _ ≤ (C * δ ^ k) * δ :=
          mul_le_mul_of_nonneg_left (by simpa only [mem_closedBall, dist_eq_norm] using hx) (by positivity)
        _ = C * δ ^ (k + 1) := by rw [pow_succ, mul_assoc]
  intro x hx j hj
  have hh := hI (m + 1 - j) (by omega) x hx
  exact ((congrArg (fun k : ℕ => ‖iteratedFDeriv ℝ k f x‖)
    (show m + 1 - (m + 1 - j) = j by omega)).symm.le.trans hh)

end CalderonPatch
