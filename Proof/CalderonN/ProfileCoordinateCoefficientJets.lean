module

public import Proof.CalderonN.ProfileChartJetExpansion
public import Proof.CalderonN.LocalSmoothJetBudget

import Mathlib.Tactic

/-! Uniform finite jets of the scalar coefficients in the coordinate
expansion of iterated covariant derivatives. -/

public section

noncomputable section
open Set
open scoped ContDiff
set_option autoImplicit false
set_option maxHeartbeats 3300000
set_option backward.isDefEq.respectTransparency false
namespace CalderonN.ProfileCovariant

variable {dim : ℕ}

private theorem baseCoefficientDerivative_jet_budget
    (f : ℝ × X dim → ℝ) (hf : ContDiff ℝ ∞ f) (x : ℝ × X dim)
    (i : I dim) (n : ℕ) (B : ℝ) (hJ : LocalSmoothJetBudget f x (n+1) B) :
    LocalSmoothJetBudget (baseCoefficientDerivative f i) x n B := by
  let L := ContinuousLinearMap.apply ℝ ℝ ((0:ℝ),axis i)
  have hL : ‖L‖ ≤ 1 := by
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro A
    simpa only [L,ContinuousLinearMap.apply_apply,Prod.norm_def,norm_zero,norm_axis,
      max_eq_right zero_le_one,mul_one,one_mul] using A.le_opNorm ((0:ℝ),axis i)
  have h := hJ.fderiv.linear_postcomp L
  have h' := h.enlarge (show ‖L‖*B ≤ B from
    (mul_le_mul_of_nonneg_right hL hJ.nonneg).trans_eq (one_mul _))
  have hEq : baseCoefficientDerivative f i = L ∘ fderiv ℝ f :=
    funext (baseCoefficientDerivative_eq_total f hf i)
  exact hEq.symm ▸ h'

@[expose] def coordinateCoefficientGrowth (m : ℕ) (C : ℝ) : ℝ :=
  1+(2:ℝ)^m*‖ContinuousLinearMap.mul ℝ ℝ‖*C

theorem covariantCoordinateExpansion_coefficient_jets
    (Γ : CoordinateConnectionFamily dim) (hΓ : ∀ k i j,ContDiff ℝ ∞ (Γ k i j))
    (x : ℝ × X dim) (M : ℕ) (C : ℝ) (hC : 0 ≤ C)
    (hJ : ∀ k i j,LocalSmoothJetBudget (Γ k i j) x M C)
    (n N : ℕ) (hN : N+n ≤ M) (I : Fin n → I dim) :
    ∀ t ∈ covariantCoordinateExpansion Γ n I,
      LocalSmoothJetBudget t.coeff x N ((coordinateCoefficientGrowth M C)^n) := by
  let D := coordinateCoefficientGrowth M C
  have hD : 1 ≤ D := by
    dsimp only [D,coordinateCoefficientGrowth]
    exact le_add_of_nonneg_right (by positivity)
  induction n generalizing N with
  | zero =>
    intro t ht
    simp only [covariantCoordinateExpansion,List.mem_cons,List.not_mem_nil,or_false] at ht
    subst t
    simpa only [pow_zero,norm_one] using
      (LocalSmoothJetBudget.const (x:=x) (N:=N) (1:ℝ))
  | succ n ih =>
    intro t ht
    simp only [covariantCoordinateExpansion,List.mem_append] at ht
    rcases ht with ht | ht
    · obtain ⟨s,hs,hst⟩ := List.mem_flatMap.mp ht
      simp only [coordinateTermDerivative,List.mem_cons,List.not_mem_nil,or_false] at hst
      rcases hst with rfl | rfl
      · have h := ih (N+1) (by omega) (Fin.tail I) s hs
        have hS := covariantCoordinateExpansion_coeff_smooth Γ hΓ n (Fin.tail I) s hs
        exact (baseCoefficientDerivative_jet_budget s.coeff hS x (I 0) N (D^n) h).enlarge
          (pow_le_pow_right₀ hD (Nat.le_succ _))
      · exact (ih N (by omega) (Fin.tail I) s hs).enlarge
          (pow_le_pow_right₀ hD (Nat.le_succ _))
    · obtain ⟨l,_,ht⟩ := List.mem_flatMap.mp ht
      obtain ⟨k,_,ht⟩ := List.mem_flatMap.mp ht
      obtain ⟨s,hs,rfl⟩ := List.mem_map.mp ht
      let G := Γ k (I 0) ((Fin.tail I) l)
      have hG : LocalSmoothJetBudget (fun z => -G z) x N C := by
        refine ⟨(hJ k _ _).smooth.neg,fun j hj => ?_⟩
        change ‖iteratedFDeriv ℝ j (-G) x‖ ≤ C
        rw [iteratedFDeriv_neg_apply,norm_neg]
        exact (hJ k _ _).bound j (by omega)
      have hS := ih N (by omega) (Function.update (Fin.tail I) l k) s hs
      have hProd := hG.bilinear hS (ContinuousLinearMap.mul ℝ ℝ)
      change LocalSmoothJetBudget (fun z => -G z*s.coeff z) x N (D^(n+1))
      apply hProd.enlarge
      rw [pow_succ']
      have hA : (2:ℝ)^N*‖ContinuousLinearMap.mul ℝ ℝ‖*C ≤ D := by
        exact (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
          (pow_le_pow_right₀ (show 1 ≤ (2:ℝ) by norm_num) (show N ≤ M by omega))
          (norm_nonneg (ContinuousLinearMap.mul ℝ ℝ))) hC).trans
          (le_add_of_nonneg_left (zero_le_one : (0:ℝ) ≤ 1))
      exact mul_le_mul_of_nonneg_right hA (pow_nonneg (zero_le_one.trans hD) _)

@[expose] def coordinateExpansionLength (dim : ℕ) : ℕ → ℕ
  | 0 => 1
  | n+1 => (2+n*dim)*coordinateExpansionLength dim n

private theorem sum_constant_natural {A : Type*} (L : List A) (a : ℕ) :
    (L.map (fun _ => a)).sum = L.length*a := by
  induction L with
  | nil => simp
  | cons t L ih => simp [ih,Nat.succ_mul,Nat.add_comm]

theorem covariantCoordinateExpansion_length (Γ : CoordinateConnectionFamily dim)
    (n : ℕ) (I : Fin n → I dim) :
    (covariantCoordinateExpansion Γ n I).length = coordinateExpansionLength dim n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simp only [covariantCoordinateExpansion,List.length_append,List.length_flatMap,
        coordinateTermDerivative,List.length_cons,List.length_nil,List.length_map,
        ih,sum_constant_natural,List.length_ofFn,coordinateExpansionLength]
      ring

end CalderonN.ProfileCovariant
