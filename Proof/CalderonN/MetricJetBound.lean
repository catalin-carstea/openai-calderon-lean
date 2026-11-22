module

public import Proof.CalderonN.Chart

import Proof.CalderonN.CoordinateJets
import Proof.CalderonN.MetricCalculus
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

public section

open Set
open scoped BigOperators ContDiff

namespace CalderonN

variable {dim : ℕ} [NeZero dim]

private theorem norm_iteratedFDeriv_hessian_product_le {U : Set (X dim)} (hU : IsOpen U)
    {y : (X dim)} (hy : y ∈ U) {A f : (X dim) → ℝ} (hA : ContDiffOn ℝ ∞ A U) (hf : ContDiffOn ℝ ∞ f U)
    {C B : ℝ} (hC : 0 ≤ C) (hB : 0 ≤ B)
    (hAjet : ∀ d ≤ 8, ‖iteratedFDeriv ℝ d A y‖ ≤ C)
    (hfjet : ∀ d ≤ 10, ‖iteratedFDeriv ℝ d f y‖ ≤ B)
    {m : ℕ} (hm : m ≤ 8) (i j : (I dim)) :
    ‖iteratedFDeriv ℝ m (fun z => A z * hessian f z i j) y‖ ≤ ((2 : ℝ)^8 * C) * B := by
  have hH : ContDiffOn ℝ ∞ (fun z => hessian f z i j) U :=
    contDiffOn_coordDeriv (contDiffOn_coordDeriv hf hU j) hU i
  have h := norm_iteratedFDerivWithin_mul_le hA hH hU.uniqueDiffOn hy (n := m) (by simp)
  rw [iteratedFDerivWithin_of_isOpen (f := fun z => A z * hessian f z i j) m hU hy] at h
  simp_rw [fun d => iteratedFDerivWithin_of_isOpen (𝕜 := ℝ) (f := A) d hU hy,
    fun d => iteratedFDerivWithin_of_isOpen (𝕜 := ℝ) (f := fun z => hessian f z i j) d hU hy] at h
  apply h.trans
  calc
    _ ≤ ∑ d ∈ Finset.range (m + 1), (m.choose d : ℝ) * (C * B) := by
      apply Finset.sum_le_sum
      intro d hd
      have hdm : d ≤ m := Nat.le_of_lt_succ (Finset.mem_range.mp hd)
      have hHB : ‖iteratedFDeriv ℝ (m - d) (fun z => hessian f z i j) y‖ ≤ B :=
        (norm_iteratedFDeriv_hessian_entry_le (hf.contDiffAt (hU.mem_nhds hy)) i j (m - d)).trans
          (hfjet _ (by omega))
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul (hAjet d (hdm.trans hm)) hHB (norm_nonneg _) hC) (by positivity)
    _ = (2 : ℝ)^m * (C * B) := by
      rw [← Finset.sum_mul, ← Nat.cast_sum, Nat.sum_range_choose, Nat.cast_pow]
      norm_num
    _ ≤ ((2 : ℝ)^8 * C) * B := by
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) hm) (mul_nonneg hC hB)

private theorem smallJet_le_of_entry_bound {γ g : MetricField dim} {y : X dim} {D : ℝ}
    (hD : 0 ≤ D)
    (h : ∀ a : I dim → Fin 9, (∑ k, (a k).val) ≤ 8 → ∀ i j : I dim,
      ‖chartPartial (fun k => (a k).val) (fun z => (principal γ g z - (γ z)⁻¹) i j) y‖ ≤ D) :
    smallJet γ g y ≤ ((dim : ℝ) * (9 : ℝ)^dim) * D := by
  let S := (Finset.univ : Finset (I dim → Fin 9)).filter (fun a => (∑ k, (a k).val) ≤ 8)
  have hCap (a : I dim → Fin 9) (ha : a ∈ S) :
      Real.sqrt (∑ i : I dim, ∑ j : I dim,
        chartPartial (fun k => (a k).val) (fun z => (principal γ g z - (γ z)⁻¹) i j) y ^ 2)
        ≤ (dim : ℝ) * D := by
    rw [Real.sqrt_le_left (by positivity)]
    calc
      _ ≤ ∑ _i : I dim, ∑ _j : I dim, D ^ 2 := by
        refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_
        have hj := h a (Finset.mem_filter.mp ha).2 i j
        rw [Real.norm_eq_abs] at hj
        exact sq_le_sq.mpr (by rwa [abs_of_nonneg hD])
      _ = _ := by simp [mul_pow]; ring
  calc
    _ ≤ ∑ _a ∈ S, (dim : ℝ) * D := Finset.sum_le_sum hCap
    _ ≤ ∑ _a : I dim → Fin 9, (dim : ℝ) * D :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (fun _ _ _ => by positivity)
    _ = _ := by simp [Fintype.card_fun]; ring

/-- The normalized metric discrepancy is controlled by the order-ten
spatial derivatives of the paired harmonic differences and the order-eight
smooth coefficients of the pointwise recovery equation. -/
theorem smallJet_le_of_hessian_recovery_model {n : ℕ} {U : Set (X dim)} (hU : IsOpen U)
    {y : (X dim)} (hy : y ∈ U) {γ g : (MetricField dim)} {V : Fin n → (X dim) → ℝ}
    (hV : ∀ a, ContDiffOn ℝ ∞ (V a) U)
    {A : ((I dim) × (I dim)) → (Fin n × (I dim) × (I dim)) → (X dim) → ℝ} (hA : ∀ q v, ContDiffOn ℝ ∞ (A q v) U)
    (heq : ∀ q : (I dim) × (I dim), EqOn (fun z => (principal γ g z - (γ z)⁻¹) q.1 q.2)
      (fun z => ∑ v : Fin n × (I dim) × (I dim), A q v z * hessian (V v.1) z v.2.1 v.2.2) U)
    {C B : ℝ} (hC : 0 ≤ C) (hB : 0 ≤ B)
    (hAc : ∀ q v d, d ≤ 8 → ‖iteratedFDeriv ℝ d (A q v) y‖ ≤ C)
    (hVc : ∀ a d, d ≤ 10 → ‖iteratedFDeriv ℝ d (V a) y‖ ≤ B) :
    smallJet γ g y ≤ ((dim : ℝ) * (9 : ℝ)^dim * Fintype.card (Fin n × (I dim) × (I dim)) * (2 : ℝ)^8 * C) * B := by
  let D := (Fintype.card (Fin n × (I dim) × (I dim)) : ℝ) * (((2 : ℝ)^8 * C) * B)
  have hD : 0 ≤ D := by positivity
  have hb : smallJet γ g y ≤ ((dim : ℝ) * (9 : ℝ)^dim) * D := by
    apply smallJet_le_of_entry_bound hD
    intro a hm i j
    let F : (X dim) → ℝ := fun z => (principal γ g z - (γ z)⁻¹) i j
    let f (v : Fin n × (I dim) × (I dim)) (z : (X dim)) :=
      A (i, j) v z * hessian (V v.1) z v.2.1 v.2.2
    have hF : EqOn F (fun z => ∑ v, f v z) U := heq (i, j)
    have hf (v : Fin n × (I dim) × (I dim)) : ContDiffOn ℝ ∞ (f v) U :=
      (hA (i, j) v).mul (contDiffOn_coordDeriv
        (contDiffOn_coordDeriv (hV v.1) hU v.2.2) hU v.2.1)
    have hs : ContDiffOn ℝ ∞ F U := (ContDiffOn.sum fun v _ => hf v).congr hF
    apply (norm_chartPartial_le hU hy hs (fun k => (a k).val)).trans
    let m := ∑ k, (a k).val
    change ‖iteratedFDeriv ℝ m F y‖ ≤ D
    have he : iteratedFDeriv ℝ m F y = ∑ v, iteratedFDeriv ℝ m (f v) y := by
      rw [← iteratedFDerivWithin_of_isOpen m hU hy, iteratedFDerivWithin_congr hF hy,
        iteratedFDerivWithin_of_isOpen m hU hy]
      exact iteratedFDeriv_fun_sum_apply fun v _ =>
        ((hf v).contDiffAt (hU.mem_nhds hy)).of_le (by simp)
    rw [he]
    calc
      _ ≤ ∑ v, ‖iteratedFDeriv ℝ m (f v) y‖ := norm_sum_le _ _
      _ ≤ ∑ _v : Fin n × (I dim) × (I dim), ((2 : ℝ)^8 * C) * B :=
        Finset.sum_le_sum fun v _ => norm_iteratedFDeriv_hessian_product_le hU hy
          (hA (i, j) v) (hV v.1) hC hB (hAc (i, j) v) (hVc v.1) hm v.2.1 v.2.2
      _ = D := by simp only [D, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  convert hb using 1
  dsimp only [D]
  ring

end CalderonN
