module

public import Proof.CalderonN.ProfileCoordinateCoefficientJets
public import Proof.CalderonN.ChartMultilinearBound

import Mathlib.Tactic

/-! Recover weighted ordinary jets from the protected covariant jets,
using the unique leading coordinate derivative. -/

public section

noncomputable section
open Set
open scoped ContDiff
set_option autoImplicit false
set_option maxHeartbeats 4700000
set_option backward.isDefEq.respectTransparency false
namespace CalderonN.ProfileCovariant

variable {dim : ℕ}

@[expose] def profileChartJetGrowth (dim : ℕ) (A D : ℝ) : ℕ → ℝ
  | 0 => 0
  | n+1 => profileChartJetGrowth dim A D n+
      (A+(coordinateExpansionLength dim (n+1):ℝ)*D^(n+1)*profileChartJetGrowth dim A D n)

theorem profileChartJetGrowth_nonneg (A D : ℝ) (hA : 0 ≤ A) (hD : 0 ≤ D) (n : ℕ) :
    0 ≤ profileChartJetGrowth dim A D n := by
  induction n with
  | zero => exact le_rfl
  | succ n ih => simp only [profileChartJetGrowth]; positivity

theorem profileChartJetGrowth_mono (A D : ℝ) (hA : 0 ≤ A) (hD : 0 ≤ D) :
    Monotone (profileChartJetGrowth dim A D) := by
  apply monotone_nat_of_le_succ
  intro n
  apply le_add_of_nonneg_right
  have h := profileChartJetGrowth_nonneg (dim:=dim) A D hA hD n
  positivity

private theorem abs_coordinateTermsValue_le_uniform
    (L : List (CoordinateJetTerm dim)) (f : X dim → ℝ) (x : ℝ × X dim) (C : ℝ)
    (h : ∀ t ∈ L,|coordinateTermValue t f x| ≤ C) :
    |coordinateTermsValue L f x| ≤ (L.length:ℝ)*C := by
  induction L with
  | nil => simp [coordinateTermsValue]
  | cons t l ih =>
    have ht := h t (by simp)
    have hl := ih (fun s hs => h s (by simp [hs]))
    simp only [coordinateTermsValue,List.map_cons,List.sum_cons,List.length_cons,Nat.cast_add,Nat.cast_one] at hl ⊢
    exact (abs_add_le _ _).trans ((add_le_add ht hl).trans_eq (by ring))

theorem abs_coordinatePartialJet_le_of_covariant_bounds
    (Γ : CoordinateConnectionFamily dim) (hΓ : ∀ k i j,ContDiff ℝ ∞ (Γ k i j))
    (x : ℝ × X dim) (M : ℕ) (G : ℝ) (hG : 0 ≤ G)
    (hJ : ∀ k i j,LocalSmoothJetBudget (Γ k i j) x M G)
    (f : X dim → ℝ) (hf : ContDiff ℝ ∞ f) (β A : ℝ) (hβ : 1 ≤ β) (hA : 0 ≤ A)
    (hCov : ∀ n ≤ M,1 ≤ n → ∀ I : Fin n → I dim,
      |covariantCoordinateJet Γ f x.1 n x.2 I| ≤ A*β^n)
    (n : ℕ) (hn : n ≤ M) (hpos : 1 ≤ n) (I : Fin n → I dim) :
    |coordinatePartialJet f n I x.2| ≤
      profileChartJetGrowth dim A (coordinateCoefficientGrowth M G) n*β^n := by
  let D := coordinateCoefficientGrowth M G
  have hD : 0 ≤ D := by dsimp only [D,coordinateCoefficientGrowth]; positivity
  induction n using Nat.strong_induction_on with
  | h n ih =>
      let L := (covariantCoordinateExpansion Γ n I).filter (fun t => !decide (t.order=n))
      let C := profileChartJetGrowth dim A D (n-1)
      have hC : 0 ≤ C := profileChartJetGrowth_nonneg A D hA hD _
      have hExp := covariantCoordinateJet_eq_partial_add_lower Γ hΓ f hf n I x
      have hStep (t : CoordinateJetTerm dim) (ht : t ∈ L) :
          |coordinateTermValue t f x| ≤ D^n*(C*β^n) := by
        have hMem := (List.mem_filter.mp ht).1
        have hLt : t.order < n := by
          have hne : t.order ≠ n := by
            simpa only [Bool.not_eq_true',decide_eq_false_iff_not] using (List.mem_filter.mp ht).2
          exact lt_of_le_of_ne (covariantCoordinateExpansion_order_le Γ n I t hMem) hne
        have hT : |t.coeff x| ≤ D^n := by
          rw [← Real.norm_eq_abs]
          exact (covariantCoordinateExpansion_coefficient_jets Γ hΓ x M G hG hJ n 0
            (by omega) I t hMem).value_norm_le
        by_cases hz : t.order = 0
        · rw [coordinateTermValue,covariantCoordinateExpansion_zero_order_coeff Γ n I hpos t hMem hz]
          simp only [Pi.zero_apply,zero_mul,abs_zero]
          positivity
        · have h₁ := ih t.order hLt (hLt.le.trans hn) (by omega) t.indices
          have hCoeff := profileChartJetGrowth_mono (dim:=dim) A D hA hD (show t.order ≤ n-1 by omega)
          have hP := pow_le_pow_right₀ hβ hLt.le
          have hNorm := (h₁.trans (mul_le_mul hCoeff hP (pow_nonneg (zero_le_one.trans hβ) _)
            hC))
          rw [coordinateTermValue,abs_mul]
          exact mul_le_mul hT hNorm (abs_nonneg _) (by positivity)
      have hLen : (L.length:ℝ) ≤ coordinateExpansionLength dim n := by
        exact_mod_cast (List.length_filter_le _ _).trans_eq (covariantCoordinateExpansion_length Γ n I)
      have hLower := (abs_coordinateTermsValue_le_uniform L f x _ hStep).trans
        (mul_le_mul_of_nonneg_right hLen (by positivity))
      have h := hCov n hn hpos I
      have hEq : coordinatePartialJet f n I x.2 =
          covariantCoordinateJet Γ f x.1 n x.2 I-coordinateTermsValue L f x := by
        rw [hExp]
        exact (add_sub_cancel_right _ _).symm
      rw [hEq]
      refine (abs_sub _ _).trans ((add_le_add h hLower).trans ?_)
      have hn' : n-1+1 = n := by omega
      rw [← hn',profileChartJetGrowth]
      change A*β^(n-1+1) + (coordinateExpansionLength dim (n-1+1):ℝ)*
          (D^(n-1+1)*(C*β^(n-1+1))) ≤
        (C+(A+(coordinateExpansionLength dim (n-1+1):ℝ)*D^(n-1+1)*C))*β^(n-1+1)
      nlinarith only [mul_nonneg hC (pow_nonneg (zero_le_one.trans hβ) (n-1+1))]

end CalderonN.ProfileCovariant
