module

public import Proof.CalderonPatch.NativeBoundaryLayerCoefficients

import Mathlib.Analysis.Calculus.IteratedDeriv.FaaDiBruno
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Tactic

public section
noncomputable section
open Filter Finset Set
open scoped ContDiff Topology Matrix.Norms.Elementwise

namespace CalderonPatch.BoundaryLayer

open CalderonN (X I Mat)

theorem iteratedDeriv_clm_left {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (L : E →L[ℝ] F)
    {f : ℝ → E} {t : ℝ} (hf : ContDiffAt ℝ ∞ f t) (k : ℕ) :
    iteratedDeriv k (L ∘ f) t = L (iteratedDeriv k f t) := by
  rw [iteratedDeriv_eq_iteratedFDeriv,L.iteratedFDeriv_comp_left hf (by simp),
    iteratedDeriv_eq_iteratedFDeriv]
  rfl

theorem iteratedDeriv_matrix_entry {n : ℕ} {f : ℝ → Mat n} {t : ℝ}
    (hf : ContDiffAt ℝ ∞ f t) (k : ℕ) (i j : I n) :
    iteratedDeriv k (fun s => f s i j) t = iteratedDeriv k f t i j :=
  iteratedDeriv_clm_left ((Matrix.entryLinearMap ℝ ℝ i j).toContinuousLinearMap) hf k

theorem iteratedDeriv_comp_congr_finite {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {f₁ f₂ : ℝ → E} {A : E → F} {t : ℝ}
    (hf₁ : ContDiffAt ℝ ∞ f₁ t) (hf₂ : ContDiffAt ℝ ∞ f₂ t)
    (hA : ContDiffAt ℝ ∞ A (f₁ t))
    (k : ℕ) (hEq : ∀ l ≤ k, iteratedDeriv l f₁ t = iteratedDeriv l f₂ t) :
    iteratedDeriv k (A ∘ f₁) t = iteratedDeriv k (A ∘ f₂) t := by
  have h₀ : f₁ t = f₂ t := by simpa only [iteratedDeriv_zero] using hEq 0 (Nat.zero_le _)
  have hA₂ : ContDiffAt ℝ ∞ A (f₂ t) := h₀ ▸ hA
  rw [iteratedDeriv_vcomp_eq_sum_orderedFinpartition hA hf₁ (by simp),
    iteratedDeriv_vcomp_eq_sum_orderedFinpartition hA₂ hf₂ (by simp)]
  apply sum_congr rfl
  intro c _
  rw [h₀]
  congr 1
  funext j
  exact hEq _ (c.partSize_le j)

theorem iteratedDeriv_mul_congr_finite {f₁ f₂ g₁ g₂ : ℝ → ℝ} {t : ℝ}
    (hf₁ : ContDiffAt ℝ ∞ f₁ t) (hf₂ : ContDiffAt ℝ ∞ f₂ t)
    (hg₁ : ContDiffAt ℝ ∞ g₁ t) (hg₂ : ContDiffAt ℝ ∞ g₂ t)
    (k : ℕ) (hF : ∀ l ≤ k, iteratedDeriv l f₁ t = iteratedDeriv l f₂ t)
    (hG : ∀ l ≤ k, iteratedDeriv l g₁ t = iteratedDeriv l g₂ t) :
    iteratedDeriv k (fun s => f₁ s * g₁ s) t = iteratedDeriv k (fun s => f₂ s * g₂ s) t := by
  rw [iteratedDeriv_fun_mul (hf₁.of_le (by simp)) (hg₁.of_le (by simp)),
    iteratedDeriv_fun_mul (hf₂.of_le (by simp)) (hg₂.of_le (by simp))]
  apply sum_congr rfl
  intro j hj
  rw [hF j (Nat.lt_succ_iff.mp (mem_range.mp hj)),hG (k-j) (Nat.sub_le _ _)]

/-- If the left factor's jets agree and only the highest jet of the
right factor differs, the product detects that difference linearly. -/
theorem iteratedDeriv_mul_top_right_difference {f₁ f₂ g₁ g₂ : ℝ → ℝ} {t : ℝ}
    (hf₁ : ContDiffAt ℝ ∞ f₁ t) (hf₂ : ContDiffAt ℝ ∞ f₂ t)
    (hg₁ : ContDiffAt ℝ ∞ g₁ t) (hg₂ : ContDiffAt ℝ ∞ g₂ t)
    (k : ℕ) (hF : ∀ l ≤ k, iteratedDeriv l f₁ t = iteratedDeriv l f₂ t)
    (hG : ∀ l < k, iteratedDeriv l g₁ t = iteratedDeriv l g₂ t) :
    iteratedDeriv k (fun s => f₁ s * g₁ s) t - iteratedDeriv k (fun s => f₂ s * g₂ s) t =
      f₁ t * (iteratedDeriv k g₁ t - iteratedDeriv k g₂ t) := by
  rw [iteratedDeriv_fun_mul (hf₁.of_le (by simp)) (hg₁.of_le (by simp)),
    iteratedDeriv_fun_mul (hf₂.of_le (by simp)) (hg₂.of_le (by simp)), ← sum_sub_distrib]
  rw [sum_eq_single 0]
  · simp only [Nat.choose_zero_right,Nat.cast_one,Nat.sub_zero,iteratedDeriv_zero,one_mul]
    have he : f₁ t = f₂ t := by simpa only [iteratedDeriv_zero] using hF 0 (Nat.zero_le _)
    rw [← he,mul_sub]
  · intro j hj hj₀
    have hjk : j ≤ k := Nat.lt_succ_iff.mp (mem_range.mp hj)
    rw [hF j hjk,hG (k-j) (by omega),sub_self]
  · intro h
    exact (h (mem_range.mpr (Nat.zero_lt_succ k))).elim

theorem contDiffAt_matrix_inv_of_det_ne_zero {n : ℕ} {A : Mat n} (hA : A.det ≠ 0) :
    ContDiffAt ℝ ∞ (fun B : Mat n => B⁻¹) A := by
  let O : Set (Mat n) := {B | B.det ≠ 0}
  have hD : Continuous (fun B : Mat n => B.det) := by
    exact (CalderonN.contDiffOn_det_of_entries (g := id)
      (fun i j => ((Matrix.entryLinearMap ℝ ℝ i j).toContinuousLinearMap).contDiff.contDiffOn)).continuousOn
      |> continuousOn_univ.mp
  have hO : IsOpen O := by
    change IsOpen ((fun B : Mat n => B.det) ⁻¹' ({0} : Set ℝ)ᶜ)
    exact isOpen_compl_singleton.preimage hD
  have h :
      ContDiffOn ℝ ∞ (fun B : Mat n => B⁻¹) O := by
    apply contDiffOn_pi.mpr
    intro i
    apply contDiffOn_pi.mpr
    intro j
    apply CalderonN.contDiffOn_inv_entry_of_entries (g := id)
    · intro i j
      exact ((Matrix.entryLinearMap ℝ ℝ i j).toContinuousLinearMap).contDiff.contDiffOn
    · exact fun B hB => hB
  exact h.contDiffAt (hO.mem_nhds hA)

end CalderonPatch.BoundaryLayer
