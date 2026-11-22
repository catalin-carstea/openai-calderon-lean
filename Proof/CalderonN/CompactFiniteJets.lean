module

public import Mathlib.Analysis.Calculus.ContDiff.Basic

import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.Calculus.FDeriv.Congr
import Mathlib.Tactic

/-! Adapted from `CompactFiniteJets` in the checked Theorem 3.1 release. -/

public section

noncomputable section
open Set Filter
open scoped ContDiff Topology

namespace CalderonN

variable {P Q F : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup Q] [NormedSpace ℝ Q] [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem exists_uniform_finite_jet_bound {J : Set P} (hJ : IsCompact J)
    {f : P → F} (hf : ContDiff ℝ ∞ f) (n : ℕ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ x ∈ J, ∀ k ≤ n, ‖iteratedFDeriv ℝ k f x‖ ≤ C := by
  choose D hD using fun k : Fin (n+1) =>
    hJ.exists_bound_of_continuousOn (hf.continuous_iteratedFDeriv (by simp : (k.val : ℕ∞ω) ≤ ∞)).continuousOn
  let C : ℝ := 1 + ∑ k, |D k|
  have hC : 1 ≤ C := le_add_of_nonneg_right (Finset.sum_nonneg fun k _ => abs_nonneg (D k))
  refine ⟨C,hC,?_⟩
  intro x hx k hk
  let j : Fin (n+1) := ⟨k,by omega⟩
  have hle : |D j| ≤ ∑ k, |D k| :=
    Finset.single_le_sum (fun i _ => abs_nonneg (D i)) (Finset.mem_univ j)
  exact (hD j x hx).trans ((le_abs_self _).trans (hle.trans (le_add_of_nonneg_left zero_le_one)))

theorem norm_iteratedFDeriv_comp_le_of_finite_bounds {g : Q → F} {f : P → Q}
    (hg : ContDiff ℝ ∞ g) (hf : ContDiff ℝ ∞ f) (x : P) {n k : ℕ} (hk : k ≤ n)
    {A B : ℝ} (hA : 0 ≤ A) (hB : 1 ≤ B)
    (hG : ∀ i ≤ n, ‖iteratedFDeriv ℝ i g (f x)‖ ≤ A)
    (hF : ∀ i ≤ n, ‖iteratedFDeriv ℝ i f x‖ ≤ B) :
    ‖iteratedFDeriv ℝ k (g ∘ f) x‖ ≤ n.factorial * A * B^n := by
  have h := norm_iteratedFDeriv_comp_le hg hf (n := k) (by simp) x
    (fun i hi => hG i (hi.trans hk))
    (fun i h₁ hi => (hF i (hi.trans hk)).trans (le_self_pow₀ hB (by omega : i ≠ 0)))
  exact h.trans (mul_le_mul
    (mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.factorial_le hk) hA)
    (pow_le_pow_right₀ hB hk) (pow_nonneg (zero_le_one.trans hB) _) (by positivity))

theorem norm_iteratedFDeriv_mul_le_of_finite_bounds {f g : P → ℝ}
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) (x : P) {n k : ℕ} (hk : k ≤ n)
    {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hF : ∀ i ≤ n, ‖iteratedFDeriv ℝ i f x‖ ≤ A)
    (hG : ∀ i ≤ n, ‖iteratedFDeriv ℝ i g x‖ ≤ B) :
    ‖iteratedFDeriv ℝ k (fun x => f x * g x) x‖ ≤ (2:ℝ)^n*(A*B) := by
  calc
    _ ≤ ∑ i ∈ Finset.range (k+1), (k.choose i : ℝ) * ‖iteratedFDeriv ℝ i f x‖ *
          ‖iteratedFDeriv ℝ (k-i) g x‖ := norm_iteratedFDeriv_mul_le hf hg x (by simp)
    _ ≤ ∑ i ∈ Finset.range (k+1), (k.choose i : ℝ)*(A*B) := by
      apply Finset.sum_le_sum
      intro i hi
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul (hF _ (by have := Finset.mem_range.mp hi; omega))
          (hG _ (by omega)) (norm_nonneg _) hA) (by positivity)
    _ = (2:ℝ)^k*(A*B) := by
      rw [← Finset.sum_mul]
      congr 1
      exact_mod_cast Nat.sum_range_choose k
    _ ≤ _ := mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) hk) (mul_nonneg hA hB)

theorem iteratedFDeriv_slice_right_eq {f : P × Q → F} (hf : ContDiff ℝ ∞ f)
    (p : P) (q : Q) (k : ℕ) :
    iteratedFDeriv ℝ k (fun q => f (p,q)) q =
      (iteratedFDeriv ℝ k f (p,q)).compContinuousLinearMap
        (fun _ => ContinuousLinearMap.inr ℝ P Q) := by
  let L := ContinuousLinearMap.inr ℝ P Q
  let b : P × Q := (p,0)
  let g (x : P × Q) := f (x+b)
  have hg : ContDiff ℝ ∞ g := hf.comp (contDiff_id.add contDiff_const)
  have h := L.iteratedFDeriv_comp_right hg q (i := k) (by simp)
  rw [show iteratedFDeriv ℝ k g (L q) = iteratedFDeriv ℝ k f (p,q) by
    simpa only [g,L,b,ContinuousLinearMap.inr_apply,Prod.mk_add_mk,zero_add,add_zero] using
      iteratedFDeriv_comp_add_right (𝕜 := ℝ) (f := f) k b (L q)] at h
  simpa [Function.comp_def,g,L,b] using h

theorem iteratedFDeriv_slice_left_eq {f : P × Q → F} (hf : ContDiff ℝ ∞ f)
    (p : P) (q : Q) (k : ℕ) :
    iteratedFDeriv ℝ k (fun p => f (p,q)) p =
      (iteratedFDeriv ℝ k f (p,q)).compContinuousLinearMap
        (fun _ => ContinuousLinearMap.inl ℝ P Q) := by
  let L := ContinuousLinearMap.inl ℝ P Q
  let b : P × Q := (0,q)
  let g (x : P × Q) := f (x+b)
  have hg : ContDiff ℝ ∞ g := hf.comp (contDiff_id.add contDiff_const)
  have h := L.iteratedFDeriv_comp_right hg p (i := k) (by simp)
  rw [show iteratedFDeriv ℝ k g (L p) = iteratedFDeriv ℝ k f (p,q) by
    simpa only [g,L,b,ContinuousLinearMap.inl_apply,Prod.mk_add_mk,add_zero,zero_add] using
      iteratedFDeriv_comp_add_right (𝕜 := ℝ) (f := f) k b (L p)] at h
  simpa [Function.comp_def,g,L,b] using h

theorem norm_iteratedFDeriv_slice_right_le {f : P × Q → F} (hf : ContDiff ℝ ∞ f)
    (p : P) (q : Q) (k : ℕ) :
    ‖iteratedFDeriv ℝ k (fun q => f (p,q)) q‖ ≤ ‖iteratedFDeriv ℝ k f (p,q)‖ := by
  rw [iteratedFDeriv_slice_right_eq hf]
  exact ContinuousMultilinearMap.norm_compContinuous_linearIsometry_le _ (fun _ => LinearIsometry.inr ℝ P Q)

end CalderonN
