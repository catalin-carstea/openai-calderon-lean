module

public import Proof.CalderonN.Coordinates
import Mathlib.Tactic

public section

/- Entrywise estimates from SmallJetBounds in the 3D Theorem 3.1 release
   (55d37bfe), now indexed by all multi-indices of order at most eight. -/
noncomputable section
open Finset

namespace CalderonN

variable {n : ℕ}

private lemma foldr_coordinateIterates_zero {A : Type*} (D : Fin n → A → A) (u : A) :
    (List.ofFn fun i => (D i)^[0]).foldr (fun L v => L v) u = u := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [List.ofFn_succ]
      simp only [List.foldr_cons, Function.iterate_zero, id_eq]
      exact ih (fun j => D j.succ)

private lemma foldr_coordinateIterates_single {A : Type*} (D : Fin n → A → A)
    (k : Fin n) (u : A) :
    (List.ofFn fun i => (D i)^[if i = k then 1 else 0]).foldr (fun L v => L v) u = D k u := by
  induction n with
  | zero => exact Fin.elim0 k
  | succ n ih =>
      induction k using Fin.cases with
      | zero =>
          rw [List.ofFn_succ]
          simp only [ite_true, List.foldr_cons, Function.iterate_one, Fin.succ_ne_zero, ite_false]
          rw [foldr_coordinateIterates_zero (fun j => D j.succ)]
      | succ k =>
          rw [List.ofFn_succ]
          simp only [
            Ne.symm (Fin.succ_ne_zero k), ite_false, Function.iterate_zero, List.foldr_cons, id_eq,
            Fin.succ_inj]
          exact ih (fun j => D j.succ) k

theorem chartPartial_zero (f : X n → ℝ) : chartPartial (fun _ => 0) f = f :=
  foldr_coordinateIterates_zero coordDeriv f

theorem chartPartial_single (k : I n) (f : X n → ℝ) :
    chartPartial (fun i => if i = k then 1 else 0) f = coordDeriv k f :=
  foldr_coordinateIterates_single coordDeriv k f

/-- Each component of every mixed partial of order at most eight is
    bounded by the protected sum of Frobenius norms. -/
theorem abs_chartPartial_principal_sub_inverse_le_smallJet
    (γ g : MetricField n) (y : X n) {a : I n → ℕ} (ha : (∑ k, a k) ≤ 8) (i j : I n) :
    |chartPartial a (fun x => (principal γ g x - (γ x)⁻¹) i j) y| ≤ smallJet γ g y := by
  let D (b : I n → ℕ) (i j : I n) :=
    chartPartial b (fun x => (principal γ g x - (γ x)⁻¹) i j) y
  let b : I n → Fin 9 := fun k => ⟨a k, by
    have hk := Finset.single_le_sum (f := a) (fun l _ => Nat.zero_le (a l)) (mem_univ k)
    omega⟩
  have hb : b ∈ (univ : Finset (I n → Fin 9)).filter (fun v => (∑ k, (v k).val) ≤ 8) :=
    mem_filter.mpr ⟨mem_univ _, ha⟩
  have h0 : (D a i j)^2 ≤ ∑ j' : I n, (D a i j')^2 :=
    single_le_sum (fun j' _ => sq_nonneg (D a i j')) (mem_univ j)
  have h1 : (∑ j' : I n, (D a i j')^2) ≤ ∑ i' : I n, ∑ j' : I n, (D a i' j')^2 :=
    single_le_sum (fun i' _ => sum_nonneg fun j' _ => sq_nonneg (D a i' j')) (mem_univ i)
  have h2 : |D a i j| ≤ Real.sqrt (∑ i' : I n, ∑ j' : I n, (D a i' j')^2) := by
    rw [← Real.sqrt_sq_eq_abs]
    exact Real.sqrt_le_sqrt (h0.trans h1)
  exact h2.trans (single_le_sum (f := fun v : I n → Fin 9 =>
    Real.sqrt (∑ i', ∑ j', (D (fun k => (v k).val) i' j')^2))
    (fun _ _ => Real.sqrt_nonneg _) hb)

theorem abs_principal_sub_inverse_entry_le_smallJet (γ g : MetricField n) (y : X n) (i j : I n) :
    |(principal γ g y - (γ y)⁻¹) i j| ≤ smallJet γ g y := by
  simpa only [chartPartial_zero] using
    abs_chartPartial_principal_sub_inverse_le_smallJet γ g y (a := fun _ => 0) (by simp) i j

theorem abs_coordDeriv_principal_sub_inverse_le_smallJet
    (γ g : MetricField n) (y : X n) (k i j : I n) :
    |coordDeriv k (fun x => (principal γ g x - (γ x)⁻¹) i j) y| ≤ smallJet γ g y := by
  simpa only [chartPartial_single] using
    abs_chartPartial_principal_sub_inverse_le_smallJet γ g y (a := fun l => if l = k then 1 else 0)
      (by simp) i j

end CalderonN
