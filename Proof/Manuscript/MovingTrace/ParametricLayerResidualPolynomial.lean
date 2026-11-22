module

/-
Adapted from the conformal Poisson Lean formalization by Cătălin I. Cârstea,
Tony Liimatainen, Yi-Hsuan Lin, and William Trad, BSD 3-Clause.
Source: arxiv-2610.13592-lean commit 4cfcab036aedbb4f825a3aeb366da12fe5673ddd.
See the source and license in references/conformal-poisson-4cfcab03.
-/
public import Proof.Manuscript.MovingTrace.ParametricLayerTrace
public import Proof.CalderonPatch.BoundaryLayerResidual
public import Mathlib.Tactic
public import Mathlib.Analysis.Calculus.ContDiff.Operations

@[expose] public section

noncomputable section
open Polynomial Set Finset
open scoped ContDiff

namespace CalderonPatch.BoundaryLayer.ParametricLayerCoefficients

variable {n : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def truncate {U : Set E} (B : ParametricLayerCoefficients (n := n) U) (R : ℕ) :
    ParametricLayerCoefficients (n := n) U where
  angularDirection := B.angularDirection
  covector := B.covector
  covector_smooth := B.covector_smooth
  kappa := B.kappa
  inverse l i j y := if l ≤ R then B.inverse l i j y else 0
  normalDrift l y := if l ≤ R then B.normalDrift l y else 0
  tangentDrift l i y := if l ≤ R then B.tangentDrift l i y else 0
  kappa_smooth := B.kappa_smooth
  kappa_pos := B.kappa_pos
  inverse_smooth l i j := by
    by_cases hl : l ≤ R
    · simpa only [ite_eq_left hl] using B.inverse_smooth l i j
    · simpa only [ite_eq_right hl] using (contDiffOn_const : ContDiffOn ℝ ∞ (fun _ : E => (0 : ℂ)) U)
  inverse_symm l i j y hy := by
    by_cases hl : l ≤ R
    · simpa only [ite_eq_left hl] using B.inverse_symm l i j y hy
    · simp only [ite_eq_right hl]
  normalDrift_smooth l := by
    by_cases hl : l ≤ R
    · simpa only [ite_eq_left hl] using B.normalDrift_smooth l
    · simpa only [ite_eq_right hl] using (contDiffOn_const : ContDiffOn ℝ ∞ (fun _ : E => (0 : ℂ)) U)
  tangentDrift_smooth l i := by
    by_cases hl : l ≤ R
    · simpa only [ite_eq_left hl] using B.tangentDrift_smooth l i
    · simpa only [ite_eq_right hl] using (contDiffOn_const : ContDiffOn ℝ ∞ (fun _ : E => (0 : ℂ)) U)
  principal_squared y hy := by
    simpa only [Nat.zero_le, ite_true] using B.principal_squared y hy

@[simp] theorem truncate_kappa {U : Set E} (B : ParametricLayerCoefficients (n := n) U)
    (R : ℕ) : (B.truncate R).kappa = B.kappa := rfl

theorem truncate_forcing_eq {U : Set E} (B : ParametricLayerCoefficients (n := n) U)
    (R j k : ℕ) (hjk : j - k ≤ R) (P : E → ℂ[X]) : (B.truncate R).forcing j k P = B.forcing j k P := by
  have h1 : j - k - 1 ≤ R := (Nat.sub_le _ _).trans hjk
  have h2 : j - k - 2 ≤ R := (Nat.sub_le _ _).trans hjk
  funext y
  simp only [forcing, principalTerm, normalTerm, crossTerm, phaseDriftTerm, tangentSecondTerm,
    tangentFirstTerm, truncate, ite_eq_left hjk, ite_eq_left h1, ite_eq_left h2]

theorem truncate_forcing_zero {U : Set E} (B : ParametricLayerCoefficients (n := n) U)
    (R j k : ℕ) (hjk : R + 2 < j - k) (P : E → ℂ[X]) : (B.truncate R).forcing j k P = 0 := by
  have h0 : ¬ j - k ≤ R := by omega
  have h1 : ¬ j - k - 1 ≤ R := by omega
  have h2 : ¬ j - k - 2 ≤ R := by omega
  funext y
  simp [forcing, principalTerm, normalTerm, crossTerm, phaseDriftTerm, tangentSecondTerm,
    tangentFirstTerm, truncate, h0, h1, h2]

def finiteResidualPolynomial {U : Set E} (B : ParametricLayerCoefficients (n := n) U)
    (a : E → ℂ) (M : ℕ) (y : E) : Polynomial (Polynomial ℂ) :=
  triangularScalePolynomial M M
    (fun j => C (2 * (B.kappa y : ℂ)) * derivative (B.layerPolynomial a j y) -
      derivative (derivative (B.layerPolynomial a j y)))
    (fun j k => (B.truncate M).forcing j k (B.layerPolynomial a k) y)

theorem layerForcing_eq_range {U : Set E} (B : ParametricLayerCoefficients (n := n) U)
    (a : E → ℂ) (j : ℕ) (y : E) :
    B.layerForcing a j y = -∑ k ∈ range j, B.forcing j k (B.layerPolynomial a k) y := by
  change -(∑ k : Fin j, (fun k : ℕ => B.forcing j k (B.layerPolynomial a k) y) k.val) = _
  exact congrArg Neg.neg (Fin.sum_univ_eq_sum_range (fun k : ℕ => B.forcing j k (B.layerPolynomial a k) y) j)

theorem finiteResidualPolynomial_coeff_zero {U : Set E} (B : ParametricLayerCoefficients (n := n) U)
    (hU : IsOpen U) {K : Set E} (hK : IsClosed K) (a : E → ℂ)
    (ha : ContDiffOn ℝ ∞ a U) (ha0 : ∀ y ∉ K, a y = 0)
    (M j : ℕ) (hj : j ≤ M) {y : E} (hy : y ∈ U) :
    (B.finiteResidualPolynomial a M y).coeff j = 0 := by
  unfold finiteResidualPolynomial
  rw [coeff_triangularScalePolynomial M M _ _ j hj (le_refl M)]
  have ht (k : ℕ) : (B.truncate M).forcing j k (B.layerPolynomial a k) y =
      B.forcing j k (B.layerPolynomial a k) y :=
    congrFun (B.truncate_forcing_eq M j k ((Nat.sub_le j k).trans hj) (B.layerPolynomial a k)) y
  simp_rw [ht]
  by_cases hj0 : j = 0
  · subst j
    simp [B.layerPolynomial_zero]
  · rw [B.layerPolynomial_transport hU hK a ha ha0 j (Nat.pos_of_ne_zero hj0) hy,
      B.layerForcing_eq_range a j y, neg_add_cancel]

theorem X_pow_dvd_finiteResidualPolynomial {U : Set E} (B : ParametricLayerCoefficients (n := n) U)
    (hU : IsOpen U) {K : Set E} (hK : IsClosed K) (a : E → ℂ)
    (ha : ContDiffOn ℝ ∞ a U) (ha0 : ∀ y ∉ K, a y = 0)
    (M : ℕ) {y : E} (hy : y ∈ U) : X ^ (M + 1) ∣ B.finiteResidualPolynomial a M y :=
  X_pow_dvd_iff.mpr (fun j hj => B.finiteResidualPolynomial_coeff_zero hU hK a ha ha0 M j (by omega) hy)

theorem finiteResidualPolynomial_coeff_regular {U : Set E} (B : ParametricLayerCoefficients (n := n) U)
    (hU : IsOpen U) {K : Set E} (hK : IsClosed K) (a : E → ℂ)
    (ha : ContDiffOn ℝ ∞ a U) (ha0 : ∀ y ∉ K, a y = 0) (M j : ℕ) :
    CoeffContDiffOn (fun y => (B.finiteResidualPolynomial a M y).coeff j) U := by
  have hp (k : ℕ) := (B.layerPolynomial_properties hU hK a ha ha0 k).1
  have hb (k : ℕ) : CoeffContDiffOn (fun y => C (2 * (B.kappa y : ℂ)) *
      derivative (B.layerPolynomial a k y) - derivative (derivative (B.layerPolynomial a k y))) U :=
    ((hp k).derivative.C_mul B.transportScale_smooth).sub (hp k).derivative.derivative
  unfold finiteResidualPolynomial triangularScalePolynomial
  simp only [coeff_add, finsetSum_coeff]
  apply CoeffContDiffOn.add
  · apply CoeffContDiffOn.sum
    intro k hk
    simp only [coeff_monomial]
    by_cases h : k = j
    · simpa only [ite_eq_left h] using hb k
    · simpa only [ite_eq_right h] using CoeffContDiffOn.const 0 U
  · apply CoeffContDiffOn.sum
    intro k hk
    apply CoeffContDiffOn.sum
    intro l hl
    by_cases hpos : 0 < l
    · simp only [ite_eq_left hpos, coeff_monomial]
      by_cases h : k + l = j
      · simpa only [ite_eq_left h] using (B.truncate M).forcing_regular hU (k + l) k (hp k)
      · simpa only [ite_eq_right h] using CoeffContDiffOn.const 0 U
    · simpa only [ite_eq_right hpos, coeff_zero] using CoeffContDiffOn.const 0 U

theorem finiteResidualPolynomial_hDegree {U : Set E} (B : ParametricLayerCoefficients (n := n) U)
    (a : E → ℂ) (M : ℕ) (y : E) : (B.finiteResidualPolynomial a M y).natDegree ≤ 2 * M + 2 := by
  exact (triangularScalePolynomial_natDegree_le M M _ _).trans (by omega)

theorem finiteResidualPolynomial_coeff_degree {U : Set E} (B : ParametricLayerCoefficients (n := n) U)
    (hU : IsOpen U) {K : Set E} (hK : IsClosed K) (a : E → ℂ)
    (ha : ContDiffOn ℝ ∞ a U) (ha0 : ∀ y ∉ K, a y = 0) (M j : ℕ) {y : E} (hy : y ∈ U) :
    ((B.finiteResidualPolynomial a M y).coeff j).natDegree ≤ 4 * M + 3 := by
  have hp (k : ℕ) := (B.layerPolynomial_properties hU hK a ha ha0 k).2.1 y hy
  have hd (k : ℕ) : (derivative (B.layerPolynomial a k y)).natDegree ≤ 2 * k :=
    (natDegree_derivative_le _).trans ((Nat.sub_le _ _).trans (hp k))
  have hdd (k : ℕ) : (derivative (derivative (B.layerPolynomial a k y))).natDegree ≤ 2 * k :=
    (natDegree_derivative_le _).trans ((Nat.sub_le _ _).trans (hd k))
  unfold finiteResidualPolynomial triangularScalePolynomial
  simp only [coeff_add, finsetSum_coeff]
  apply natDegree_add_le_of_degree_le
  · apply natDegree_sum_le_of_forall_le
    intro k hk
    simp only [coeff_monomial]
    split_ifs
    · exact (natDegree_sub_le _ _).trans (max_le
        ((natDegree_C_mul_le _ _).trans (hd k)) (hdd k)) |>.trans (by have hh := Finset.mem_range.mp hk; omega)
    · simp
  · apply natDegree_sum_le_of_forall_le
    intro k hk
    apply natDegree_sum_le_of_forall_le
    intro l hl
    by_cases hpos : 0 < l
    · simp only [ite_eq_left hpos, coeff_monomial]
      split_ifs
      · exact ((B.truncate M).forcing_degree (k + l) k (by omega) _ (hp k)).trans
          (by have hh := Finset.mem_range.mp hk; have hh' := Finset.mem_range.mp hl; omega)
      · simp
    · simp only [ite_eq_right hpos, coeff_zero, natDegree_zero]
      omega

def finiteResidualProfile {U : Set E} (B : ParametricLayerCoefficients (n := n) U)
    (a : E → ℂ) (M : ℕ) (h : ℝ) (x : E × ℝ) : ℂ :=
  ∑ j : Fin (2 * M + 3), (h ^ j.val : ℂ) *
    polynomialProfile (B.kappa x.1) ((B.finiteResidualPolynomial a M x.1).coeff j.val) x.2

theorem finiteResidualProfile_eq_eval {U : Set E} (B : ParametricLayerCoefficients (n := n) U)
    (a : E → ℂ) (M : ℕ) (h : ℝ) (y : E) (s : ℝ) :
    B.finiteResidualProfile a M h (y, s) = profileScaleEval (B.kappa y) (B.finiteResidualPolynomial a M y) h s :=
  (profileScaleEval_eq_coeff_sum (B.kappa y) _ (2 * M + 3)
    ((B.finiteResidualPolynomial_hDegree a M y).trans_lt (by omega)) h s).symm

theorem finiteResidualProfile_eq_double_sum {U : Set E} (B : ParametricLayerCoefficients (n := n) U)
    (a : E → ℂ) (M : ℕ) (h : ℝ) (y : E) (s : ℝ) :
    B.finiteResidualProfile a M h (y, s) =
      (∑ k ∈ range (M + 1), (h ^ k : ℂ) * polynomialProfile (B.kappa y)
        (C (2 * (B.kappa y : ℂ)) * derivative (B.layerPolynomial a k y) -
          derivative (derivative (B.layerPolynomial a k y))) s) +
      ∑ k ∈ range (M + 1), ∑ l ∈ range (M + 3),
        if 0 < l then (h ^ (k + l) : ℂ) * polynomialProfile (B.kappa y)
          ((B.truncate M).forcing (k + l) k (B.layerPolynomial a k) y) s else 0 := by
  rw [B.finiteResidualProfile_eq_eval]
  unfold finiteResidualPolynomial triangularScalePolynomial
  rw [profileScaleEval_add, profileScaleEval_sum, profileScaleEval_sum]
  congr 1
  · apply sum_congr rfl
    intro k hk
    exact profileScaleEval_monomial _ _ _ _ _
  · apply sum_congr rfl
    intro k hk
    rw [profileScaleEval_sum]
    apply sum_congr rfl
    intro l hl
    by_cases hpos : 0 < l
    · simp only [ite_eq_left hpos, profileScaleEval_monomial]
    · simp only [ite_eq_right hpos, profileScaleEval_zero]

end CalderonPatch.BoundaryLayer.ParametricLayerCoefficients
