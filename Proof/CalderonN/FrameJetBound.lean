module

public import Proof.CalderonN.Coercivity

import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset

@[expose] public section

noncomputable section
open scoped BigOperators

namespace CalderonN

variable {dim : ℕ}

/-- The frame tensor norm is obtained by contracting all the coordinate
components. A bound on the frame entries gives a uniform conversion. -/
theorem jetNorm_le_of_component_bound (γ : (MetricField dim)) (e : (Frame dim)) (f : (X dim) → ℝ) (y : (X dim))
    (n : ℕ) {A E : ℝ} (hA : 0 ≤ A) (hE : 0 ≤ E)
    (he : ∀ i j, |e y i j| ≤ E)
    (hjet : ∀ b : Fin n → (I dim), |covJet γ f n y b| ≤ A) :
    jetNorm γ e f n y ≤ Real.sqrt (Fintype.card (Fin n → (I dim))) *
      (Fintype.card (Fin n → (I dim)) * A * E ^ n) := by
  let J := Fin n → (I dim)
  let N := Fintype.card J
  let B : ℝ := (N : ℝ) * (A * E ^ n)
  have hB : 0 ≤ B := by dsimp only [B]; positivity
  let T (a b : J) := covJet γ f n y b * ∏ t, e y (a t) (b t)
  have hterm (a b : J) : |T a b| ≤ A * E ^ n := by
    simp only [T, abs_mul, Finset.abs_prod]
    apply mul_le_mul (hjet b) _ (Finset.prod_nonneg fun _ _ => abs_nonneg _) hA
    calc
      _ ≤ ∏ _t : Fin n, E := Finset.prod_le_prod₀ (fun _ _ => abs_nonneg _) fun t _ => he (a t) (b t)
      _ = _ := by simp
  have hc (a : J) : |∑ b : J, T a b| ≤ B := by
    calc
      _ ≤ ∑ b : J, |T a b| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _b : J, A * E ^ n := Finset.sum_le_sum fun b _ => hterm a b
      _ = _ := by simp only [B, N, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hsum : (∑ a : J, (∑ b : J, T a b)^2) ≤ (N : ℝ) * B^2 := by
    calc
      _ ≤ ∑ _a : J, B^2 := Finset.sum_le_sum fun a _ => sq_le_sq.mpr (by
        rw [abs_of_nonneg hB]
        exact hc a)
      _ = _ := by simp only [N, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  change Real.sqrt (∑ a : J, (∑ b : J, T a b)^2) ≤ _
  apply (Real.sqrt_le_sqrt hsum).trans_eq
  rw [Real.sqrt_mul (Nat.cast_nonneg _), Real.sqrt_sq hB]
  dsimp only [B, N, J]
  ring

end CalderonN
