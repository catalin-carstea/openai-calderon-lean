/-
Adapted from the conformal Poisson Lean formalization by Cătălin I. Cârstea,
Tony Liimatainen, Yi-Hsuan Lin, and William Trad, BSD 3-Clause.
Source: arxiv-2610.13592-lean commit 4cfcab036aedbb4f825a3aeb366da12fe5673ddd.
See the source and license in references/conformal-poisson-4cfcab03.
-/
module

public import Proof.CalderonPatch.BoundaryLayerWaves

import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Tactic

public section

noncomputable section

open Polynomial Set Finset
open scoped ContDiff
namespace CalderonPatch.BoundaryLayer.BoundaryLayerCoefficients
variable {n : ℕ}
local notation "Y" => EuclideanSpace ℝ (Fin n)

@[expose] def truncate {ξ : Fin n → ℝ} {U : Set Y} (B : BoundaryLayerCoefficients ξ U) (R : ℕ) :
    BoundaryLayerCoefficients ξ U where
  kappa := B.kappa
  inverse l i j y := if l ≤ R then B.inverse l i j y else 0
  normalDrift l y := if l ≤ R then B.normalDrift l y else 0
  tangentDrift l i y := if l ≤ R then B.tangentDrift l i y else 0
  kappa_smooth := B.kappa_smooth
  kappa_pos := B.kappa_pos
  inverse_smooth l i j := by
    by_cases hl : l ≤ R
    · simpa only [if_pos hl] using B.inverse_smooth l i j
    · simpa only [if_neg hl] using (contDiffOn_const : ContDiffOn ℝ ∞ (fun _ : Y => (0 : ℂ)) U)
  inverse_symm l i j y hy := by
    by_cases hl : l ≤ R
    · simpa only [if_pos hl] using B.inverse_symm l i j y hy
    · simp only [if_neg hl]
  normalDrift_smooth l := by
    by_cases hl : l ≤ R
    · simpa only [if_pos hl] using B.normalDrift_smooth l
    · simpa only [if_neg hl] using (contDiffOn_const : ContDiffOn ℝ ∞ (fun _ : Y => (0 : ℂ)) U)
  tangentDrift_smooth l i := by
    by_cases hl : l ≤ R
    · simpa only [if_pos hl] using B.tangentDrift_smooth l i
    · simpa only [if_neg hl] using (contDiffOn_const : ContDiffOn ℝ ∞ (fun _ : Y => (0 : ℂ)) U)
  principal_squared y hy := by
    simpa only [Nat.zero_le, if_true] using B.principal_squared y hy

@[simp] theorem truncate_kappa {ξ : Fin n → ℝ} {U : Set Y} (B : BoundaryLayerCoefficients ξ U)
    (R : ℕ) : (B.truncate R).kappa = B.kappa := rfl

theorem truncate_forcing_eq {ξ : Fin n → ℝ} {U : Set Y} (B : BoundaryLayerCoefficients ξ U)
    (R j k : ℕ) (hjk : j - k ≤ R) (P : Y → ℂ[X]) : (B.truncate R).forcing j k P = B.forcing j k P := by
  have h1 : j - k - 1 ≤ R := (Nat.sub_le _ _).trans hjk
  have h2 : j - k - 2 ≤ R := (Nat.sub_le _ _).trans hjk
  funext y
  simp only [forcing, principalTerm, normalTerm, crossTerm, phaseDriftTerm, tangentSecondTerm,
    tangentFirstTerm, truncate, if_pos hjk, if_pos h1, if_pos h2]

theorem truncate_forcing_zero {ξ : Fin n → ℝ} {U : Set Y} (B : BoundaryLayerCoefficients ξ U)
    (R j k : ℕ) (hjk : R + 2 < j - k) (P : Y → ℂ[X]) : (B.truncate R).forcing j k P = 0 := by
  have h0 : ¬ j - k ≤ R := by omega
  have h1 : ¬ j - k - 1 ≤ R := by omega
  have h2 : ¬ j - k - 2 ≤ R := by omega
  funext y
  simp [forcing, principalTerm, normalTerm, crossTerm, phaseDriftTerm, tangentSecondTerm,
    tangentFirstTerm, truncate, h0, h1, h2]

end CalderonPatch.BoundaryLayer.BoundaryLayerCoefficients

open Polynomial Finset
namespace CalderonPatch.BoundaryLayer
variable {Rng : Type*} [CommRing Rng]

@[expose] def triangularScalePolynomial (M T : ℕ) (base : ℕ → Rng) (term : ℕ → ℕ → Rng) : Rng[X] :=
  (∑ k ∈ range (M + 1), monomial k (base k)) +
    ∑ k ∈ range (M + 1), ∑ l ∈ range (T + 3),
      if 0 < l then monomial (k + l) (term (k + l) k) else 0

theorem coeff_triangularScalePolynomial (M T : ℕ) (base : ℕ → Rng) (term : ℕ → ℕ → Rng)
    (j : ℕ) (hj : j ≤ M) (hMT : M ≤ T) :
    (triangularScalePolynomial M T base term).coeff j = base j + ∑ k ∈ range j, term j k := by
  have hbase : (∑ k ∈ range (M + 1), monomial k (base k)).coeff j = base j := by
    rw [finsetSum_coeff, sum_eq_single j]
    · simp
    · intro k hk hkj
      simp only [coeff_monomial, Finsupp.single_apply, if_neg hkj]
    · intro hnot
      exact (hnot (Finset.mem_range.mpr (by omega))).elim
  have hinner (k : ℕ) : (∑ l ∈ range (T + 3),
      if 0 < l then monomial (k + l) (term (k + l) k) else 0).coeff j =
        if k < j then term j k else 0 := by
    rw [finsetSum_coeff]
    by_cases hkj : k < j
    · rw [if_pos hkj, sum_eq_single (j - k)]
      · have he : k + (j - k) = j := by omega
        simp only [if_pos (by omega : 0 < j - k), he, coeff_monomial, Finsupp.single_eq_same, if_true]
      · intro l hl hlne
        by_cases hpos : 0 < l
        · have hne : k + l ≠ j := by omega
          simp only [if_pos hpos, coeff_monomial, Finsupp.single_apply, if_neg hne]
        · simp only [if_neg hpos, coeff_zero]
      · intro hn
        exact (hn (Finset.mem_range.mpr (by omega))).elim
    · rw [if_neg hkj]
      apply sum_eq_zero
      intro l hl
      by_cases hpos : 0 < l
      · have hne : k + l ≠ j := by omega
        simp only [if_pos hpos, coeff_monomial, Finsupp.single_apply, if_neg hne]
      · simp only [if_neg hpos, coeff_zero]
  have hfilter : (range (M + 1)).filter (fun k => k < j) = range j := by
    ext k
    simp only [mem_filter, Finset.mem_range]
    omega
  unfold triangularScalePolynomial
  rw [coeff_add, hbase, finsetSum_coeff]
  simp_rw [hinner]
  rw [← sum_filter, hfilter]

theorem triangularScalePolynomial_natDegree_le (M T : ℕ) (base : ℕ → Rng) (term : ℕ → ℕ → Rng) :
    (triangularScalePolynomial M T base term).natDegree ≤ M + T + 2 := by
  apply natDegree_add_le_of_degree_le
  · apply natDegree_sum_le_of_forall_le
    intro k hk
    exact (natDegree_monomial_le (base k)).trans (by have hh := Finset.mem_range.mp hk; omega)
  · apply natDegree_sum_le_of_forall_le
    intro k hk
    apply natDegree_sum_le_of_forall_le
    intro l hl
    split_ifs
    · exact (natDegree_monomial_le (term (k + l) k)).trans (by have hh := Finset.mem_range.mp hk; have hh' := Finset.mem_range.mp hl; omega)
    · simp

end CalderonPatch.BoundaryLayer

open Polynomial Set Finset
open scoped ContDiff
namespace CalderonPatch.BoundaryLayer.BoundaryLayerCoefficients
variable {n : ℕ}
local notation "Y" => EuclideanSpace ℝ (Fin n)

@[expose] def finiteResidualPolynomial {ξ : Fin n → ℝ} {U : Set Y} (B : BoundaryLayerCoefficients ξ U)
    (a : Y → ℂ) (M : ℕ) (y : Y) : Polynomial (Polynomial ℂ) :=
  triangularScalePolynomial M M
    (fun j => C (2 * (B.kappa y : ℂ)) * derivative (B.layerPolynomial a j y) -
      derivative (derivative (B.layerPolynomial a j y)))
    (fun j k => (B.truncate M).forcing j k (B.layerPolynomial a k) y)

theorem layerForcing_eq_range {ξ : Fin n → ℝ} {U : Set Y} (B : BoundaryLayerCoefficients ξ U)
    (a : Y → ℂ) (j : ℕ) (y : Y) :
    B.layerForcing a j y = -∑ k ∈ range j, B.forcing j k (B.layerPolynomial a k) y := by
  change -(∑ k : Fin j, (fun k : ℕ => B.forcing j k (B.layerPolynomial a k) y) k.val) = _
  exact congrArg Neg.neg (Fin.sum_univ_eq_sum_range (fun k : ℕ => B.forcing j k (B.layerPolynomial a k) y) j)

theorem finiteResidualPolynomial_coeff_zero {ξ : Fin n → ℝ} {U : Set Y} (B : BoundaryLayerCoefficients ξ U)
    (hU : IsOpen U) {K : Set Y} (hK : IsClosed K) (a : Y → ℂ)
    (ha : ContDiffOn ℝ ∞ a U) (ha0 : ∀ y ∉ K, a y = 0)
    (M j : ℕ) (hj : j ≤ M) {y : Y} (hy : y ∈ U) :
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

theorem X_pow_dvd_finiteResidualPolynomial {ξ : Fin n → ℝ} {U : Set Y} (B : BoundaryLayerCoefficients ξ U)
    (hU : IsOpen U) {K : Set Y} (hK : IsClosed K) (a : Y → ℂ)
    (ha : ContDiffOn ℝ ∞ a U) (ha0 : ∀ y ∉ K, a y = 0)
    (M : ℕ) {y : Y} (hy : y ∈ U) : X ^ (M + 1) ∣ B.finiteResidualPolynomial a M y :=
  X_pow_dvd_iff.mpr (fun j hj => B.finiteResidualPolynomial_coeff_zero hU hK a ha ha0 M j (by omega) hy)

end CalderonPatch.BoundaryLayer.BoundaryLayerCoefficients

open Polynomial Set Finset
open scoped ContDiff
namespace CalderonPatch.BoundaryLayer.BoundaryLayerCoefficients
variable {n : ℕ}
local notation "Y" => EuclideanSpace ℝ (Fin n)

theorem finiteResidualPolynomial_coeff_regular {ξ : Fin n → ℝ} {U : Set Y} (B : BoundaryLayerCoefficients ξ U)
    (hU : IsOpen U) {K : Set Y} (hK : IsClosed K) (a : Y → ℂ)
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
    simp only [coeff_monomial, Finsupp.single_apply]
    by_cases h : k = j
    · simpa only [if_pos h] using hb k
    · simpa only [if_neg h] using CoeffContDiffOn.const 0 U
  · apply CoeffContDiffOn.sum
    intro k hk
    apply CoeffContDiffOn.sum
    intro l hl
    by_cases hpos : 0 < l
    · simp only [if_pos hpos, coeff_monomial, Finsupp.single_apply]
      by_cases h : k + l = j
      · simpa only [if_pos h] using (B.truncate M).forcing_regular hU (k + l) k (hp k)
      · simpa only [if_neg h] using CoeffContDiffOn.const 0 U
    · simpa only [if_neg hpos, coeff_zero] using CoeffContDiffOn.const 0 U

theorem finiteResidualPolynomial_hDegree {ξ : Fin n → ℝ} {U : Set Y} (B : BoundaryLayerCoefficients ξ U)
    (a : Y → ℂ) (M : ℕ) (y : Y) : (B.finiteResidualPolynomial a M y).natDegree ≤ 2 * M + 2 := by
  exact (triangularScalePolynomial_natDegree_le M M _ _).trans (by omega)

theorem finiteResidualPolynomial_coeff_degree {ξ : Fin n → ℝ} {U : Set Y} (B : BoundaryLayerCoefficients ξ U)
    (hU : IsOpen U) {K : Set Y} (hK : IsClosed K) (a : Y → ℂ)
    (ha : ContDiffOn ℝ ∞ a U) (ha0 : ∀ y ∉ K, a y = 0) (M j : ℕ) {y : Y} (hy : y ∈ U) :
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
    simp only [coeff_monomial, Finsupp.single_apply]
    split_ifs
    · exact (natDegree_sub_le _ _).trans (max_le
        ((natDegree_C_mul_le _ _).trans (hd k)) (hdd k)) |>.trans (by have hh := Finset.mem_range.mp hk; omega)
    · simp
  · apply natDegree_sum_le_of_forall_le
    intro k hk
    apply natDegree_sum_le_of_forall_le
    intro l hl
    by_cases hpos : 0 < l
    · simp only [if_pos hpos, coeff_monomial, Finsupp.single_apply]
      split_ifs
      · exact ((B.truncate M).forcing_degree (k + l) k (by omega) _ (hp k)).trans
          (by have hh := Finset.mem_range.mp hk; have hh' := Finset.mem_range.mp hl; omega)
      · simp
    · simp only [if_neg hpos, coeff_zero, natDegree_zero]
      omega

end CalderonPatch.BoundaryLayer.BoundaryLayerCoefficients

open Polynomial Set Finset
open scoped ContDiff
namespace CalderonPatch.BoundaryLayer
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem exists_uniform_finite_power_profile_bound
    {U K : Set E} (hK : IsCompact K) (hKU : K ⊆ U)
    {κ : E → ℝ} (hκ : ContDiffOn ℝ ∞ κ U) (hpos : ∀ y ∈ U, 0 < κ y)
    (H M : ℕ) (P : Fin H → E → ℂ[X]) (D : Fin H → ℕ)
    (hP : ∀ j, CoeffContDiffOn (P j) U) (hD : ∀ j y, y ∈ K → (P j y).natDegree < D j)
    (hzero : ∀ j : Fin H, j.val ≤ M → ∀ y ∈ K, P j y = 0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ y ∈ K, ∀ h : ℝ, 0 < h → h ≤ 1 → ∀ s : ℝ, 0 ≤ s →
      ‖∑ j : Fin H, (h ^ j.val : ℂ) * polynomialProfile (κ y) (P j y) s‖ ≤ C * h ^ (M + 1) := by
  obtain ⟨c, B, hc, hB, hb⟩ := exists_uniform_finite_profile_exp_bound hK hKU hκ hpos P hP D hD
  refine ⟨(H : ℝ) * B, mul_nonneg (Nat.cast_nonneg _) hB, ?_⟩
  intro y hy h hh hh1 s hs
  have hterm (j : Fin H) : ‖(h ^ j.val : ℂ) * polynomialProfile (κ y) (P j y) s‖ ≤ B * h ^ (M + 1) := by
    by_cases hj : j.val ≤ M
    · simp only [hzero j hj y hy, polynomialProfile, eval_zero, smul_zero, mul_zero, norm_zero]
      exact mul_nonneg hB (pow_nonneg hh.le _)
    · have hpw : h ^ j.val ≤ h ^ (M + 1) := pow_le_pow_of_le_one hh.le hh1 (by omega)
      have hv : ‖polynomialProfile (κ y) (P j y) s‖ ≤ B :=
        (hb j y hy s hs).trans (by
          have he : Real.exp (-c * s) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
          simpa only [mul_one] using mul_le_mul_of_nonneg_left he hB)
      rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hh]
      calc
        _ ≤ h ^ (M + 1) * ‖polynomialProfile (κ y) (P j y) s‖ :=
          mul_le_mul_of_nonneg_right hpw (norm_nonneg _)
        _ ≤ h ^ (M + 1) * B := mul_le_mul_of_nonneg_left hv (pow_nonneg hh.le _)
        _ = _ := by ring
  calc
    _ ≤ ∑ j : Fin H, ‖(h ^ j.val : ℂ) * polynomialProfile (κ y) (P j y) s‖ := norm_sum_le _ _
    _ ≤ ∑ _j : Fin H, B * h ^ (M + 1) := sum_le_sum (fun j _ => hterm j)
    _ = _ := by simp [mul_assoc]

namespace BoundaryLayerCoefficients
variable {n : ℕ}
local notation "Y" => EuclideanSpace ℝ (Fin n)

@[expose] def finiteResidualProfile {ξ : Fin n → ℝ} {U : Set Y} (B : BoundaryLayerCoefficients ξ U)
    (a : Y → ℂ) (M : ℕ) (h : ℝ) (x : Y × ℝ) : ℂ :=
  ∑ j : Fin (2 * M + 3), (h ^ j.val : ℂ) *
    polynomialProfile (B.kappa x.1) ((B.finiteResidualPolynomial a M x.1).coeff j.val) x.2

theorem finiteResidualProfile_bound {ξ : Fin n → ℝ} {U : Set Y} (B : BoundaryLayerCoefficients ξ U)
    (hU : IsOpen U) {K : Set Y} (hK : IsCompact K) (hKU : K ⊆ U) (a : Y → ℂ)
    (ha : ContDiffOn ℝ ∞ a U) (ha0 : ∀ y ∉ K, a y = 0) (M : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ y ∈ K, ∀ h : ℝ, 0 < h → h ≤ 1 → ∀ s : ℝ, 0 ≤ s →
      ‖B.finiteResidualProfile a M h (y, s)‖ ≤ C * h ^ (M + 1) :=
  exists_uniform_finite_power_profile_bound hK hKU B.kappa_smooth B.kappa_pos (2 * M + 3) M
    (fun j y => (B.finiteResidualPolynomial a M y).coeff j.val) (fun _ => 4 * M + 4)
    (fun j => B.finiteResidualPolynomial_coeff_regular hU hK.isClosed a ha ha0 M j.val)
    (fun j y hy => (B.finiteResidualPolynomial_coeff_degree hU hK.isClosed a ha ha0 M j.val (hKU hy)).trans_lt (by omega))
    (fun j hj y hy => B.finiteResidualPolynomial_coeff_zero hU hK.isClosed a ha ha0 M j.val hj (hKU hy))

end BoundaryLayerCoefficients
end CalderonPatch.BoundaryLayer

open Polynomial Finset Set
open scoped ContDiff
namespace CalderonPatch.BoundaryLayer

@[expose] def profileScaleEval (κ : ℝ) (p : Polynomial (Polynomial ℂ)) (h s : ℝ) : ℂ :=
  polynomialProfile κ (p.eval (C (h : ℂ))) s

theorem profileScaleEval_add (κ : ℝ) (p q : Polynomial (Polynomial ℂ)) (h s : ℝ) :
    profileScaleEval κ (p + q) h s = profileScaleEval κ p h s + profileScaleEval κ q h s := by
  unfold profileScaleEval
  rw [eval_add, polynomialProfile_add]

theorem profileScaleEval_sum {ι : Type*} (κ : ℝ) (A : Finset ι)
    (p : ι → Polynomial (Polynomial ℂ)) (h s : ℝ) :
    profileScaleEval κ (∑ i ∈ A, p i) h s = ∑ i ∈ A, profileScaleEval κ (p i) h s := by
  unfold profileScaleEval
  rw [eval_finsetSum, polynomialProfile_sum]

theorem profileScaleEval_zero (κ h s : ℝ) : profileScaleEval κ 0 h s = 0 := by
  simp [profileScaleEval, polynomialProfile]

theorem profileScaleEval_monomial (κ : ℝ) (k : ℕ) (p : ℂ[X]) (h s : ℝ) :
    profileScaleEval κ (monomial k p) h s = (h ^ k : ℂ) * polynomialProfile κ p s := by
  unfold profileScaleEval
  rw [eval_monomial]
  have he : p * (C (h : ℂ)) ^ k = C ((h : ℂ) ^ k) * p := by
    rw [map_pow]
    ring
  rw [he, polynomialProfile_C_mul]

theorem profileScaleEval_eq_coeff_sum (κ : ℝ) (p : Polynomial (Polynomial ℂ))
    (H : ℕ) (hp : p.natDegree < H) (h s : ℝ) :
    profileScaleEval κ p h s = ∑ j : Fin H, (h ^ j.val : ℂ) * polynomialProfile κ (p.coeff j.val) s := by
  have he := Fin.sum_univ_eq_sum_range
    (fun j : ℕ => (h ^ j : ℂ) * polynomialProfile κ (p.coeff j) s) H
  rw [he]
  unfold profileScaleEval
  rw [eval_eq_sum_range' hp, polynomialProfile_sum]
  apply sum_congr rfl
  intro j hj
  have hjp : p.coeff j * (C (h : ℂ)) ^ j = C ((h : ℂ) ^ j) * p.coeff j := by
    rw [map_pow]
    ring
  rw [hjp, polynomialProfile_C_mul]

namespace BoundaryLayerCoefficients
variable {n : ℕ}
local notation "Y" => EuclideanSpace ℝ (Fin n)

theorem finiteResidualProfile_eq_eval {ξ : Fin n → ℝ} {U : Set Y} (B : BoundaryLayerCoefficients ξ U)
    (a : Y → ℂ) (M : ℕ) (h : ℝ) (y : Y) (s : ℝ) :
    B.finiteResidualProfile a M h (y, s) = profileScaleEval (B.kappa y) (B.finiteResidualPolynomial a M y) h s :=
  (profileScaleEval_eq_coeff_sum (B.kappa y) _ (2 * M + 3)
    ((B.finiteResidualPolynomial_hDegree a M y).trans_lt (by omega)) h s).symm

theorem finiteResidualProfile_eq_double_sum {ξ : Fin n → ℝ} {U : Set Y} (B : BoundaryLayerCoefficients ξ U)
    (a : Y → ℂ) (M : ℕ) (h : ℝ) (y : Y) (s : ℝ) :
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
    · simp only [if_pos hpos, profileScaleEval_monomial]
    · simp only [if_neg hpos, profileScaleEval_zero]

end BoundaryLayerCoefficients
end CalderonPatch.BoundaryLayer

open Finset
namespace CalderonPatch.BoundaryLayer
variable {K : Type*} [CommRing K]

theorem finite_shifted_power_sum (M d : ℕ) (hd : d ≤ 2) (h : K) (f : ℕ → K) :
    (∑ l ∈ range (M + 3), if d ≤ l then h ^ l * (if l - d ≤ M then f (l - d) else 0) else 0) =
      h ^ d * ∑ m ∈ range (M + 1), h ^ m * f m := by
  let g : ℕ → K := fun l => if d ≤ l then h ^ l * (if l - d ≤ M then f (l - d) else 0) else 0
  have hn : M + 3 = d + (M + 3 - d) := by omega
  have hhead : (∑ l ∈ range d, g l) = 0 := by
    apply sum_eq_zero
    intro l hl
    exact if_neg (by have hh := Finset.mem_range.mp hl; omega)
  have hsub : range (M + 1) ⊆ range (M + 3 - d) := range_mono (by omega)
  have htrim : (∑ m ∈ range (M + 3 - d), h ^ (d + m) * (if m ≤ M then f m else 0)) =
      ∑ m ∈ range (M + 1), h ^ (d + m) * f m := by
    calc
      _ = ∑ m ∈ range (M + 1), h ^ (d + m) * (if m ≤ M then f m else 0) := by
        symm
        apply sum_subset hsub
        intro m hm hnmem
        have he : ¬m ≤ M := by simpa only [Finset.mem_range, Nat.lt_succ_iff] using hnmem
        simp only [if_neg he, mul_zero]
      _ = _ := by
        apply sum_congr rfl
        intro m hm
        rw [if_pos (by have hh := Finset.mem_range.mp hm; omega)]
  change (∑ l ∈ range (M + 3), g l) = _
  calc
    _ = (∑ l ∈ range d, g l) + ∑ m ∈ range (M + 3 - d), g (d + m) := by
      simpa only [← hn] using (sum_range_add g d (M + 3 - d))
    _ = ∑ m ∈ range (M + 3 - d), h ^ (d + m) * (if m ≤ M then f m else 0) := by
      rw [hhead, zero_add]
      apply sum_congr rfl
      intro m hm
      simp only [g, Nat.le_add_right, if_true, Nat.add_sub_cancel_left]
    _ = ∑ m ∈ range (M + 1), h ^ (d + m) * f m := htrim
    _ = _ := by
      simp only [pow_add, mul_sum, mul_assoc]

theorem positive_finite_sum (N : ℕ) (f : ℕ → K) :
    (∑ l ∈ range (N + 1), if 0 < l then f l else 0) = (∑ l ∈ range (N + 1), f l) - f 0 := by
  rw [sum_range_succ', sum_range_succ']
  simp only [lt_self_iff_false, if_false, Nat.zero_lt_succ, if_true, zero_add]
  ring

theorem positive_truncated_power_sum (M : ℕ) (h : K) (f : ℕ → K) :
    (∑ l ∈ range (M + 3), if 0 < l then h ^ l * (if l ≤ M then f l else 0) else 0) =
      (∑ l ∈ range (M + 1), h ^ l * f l) - f 0 := by
  rw [show M + 3 = (M + 2) + 1 by omega, positive_finite_sum]
  have he := finite_shifted_power_sum M 0 (by omega) h f
  simp only [Nat.zero_le, if_true, Nat.sub_zero, pow_zero, one_mul] at he
  rw [show (M + 2) + 1 = M + 3 by omega, he]
  simp only [pow_zero, Nat.zero_le, if_true, one_mul]

end CalderonPatch.BoundaryLayer

open Polynomial Set
namespace CalderonPatch.BoundaryLayer.BoundaryLayerCoefficients
variable {n : ℕ}
local notation "Y" => EuclideanSpace ℝ (Fin n)

theorem truncate_principalTerm {ξ : Fin n → ℝ} {U : Set Y} (B : BoundaryLayerCoefficients ξ U)
    (M l : ℕ) (P : Y → ℂ[X]) (y : Y) :
    (B.truncate M).principalTerm l P y = if l ≤ M then B.principalTerm l P y else 0 := by
  by_cases hl : l ≤ M <;> simp [principalTerm, truncate, hl]

theorem truncate_normalTerm {ξ : Fin n → ℝ} {U : Set Y} (B : BoundaryLayerCoefficients ξ U)
    (M l : ℕ) (P : Y → ℂ[X]) (y : Y) :
    (B.truncate M).normalTerm l P y = if l - 1 ≤ M then B.normalTerm l P y else 0 := by
  by_cases hl : l - 1 ≤ M <;> simp [normalTerm, truncate, hl]

theorem truncate_crossTerm {ξ : Fin n → ℝ} {U : Set Y} (B : BoundaryLayerCoefficients ξ U)
    (M l d : ℕ) (P : Y → ℂ[X]) (y : Y) :
    (B.truncate M).crossTerm l d P y = if l - 1 ≤ M then B.crossTerm l d P y else 0 := by
  by_cases hl : l - 1 ≤ M <;> simp [crossTerm, truncate, hl]

theorem truncate_phaseDriftTerm {ξ : Fin n → ℝ} {U : Set Y} (B : BoundaryLayerCoefficients ξ U)
    (M l : ℕ) (P : Y → ℂ[X]) (y : Y) :
    (B.truncate M).phaseDriftTerm l P y = if l - 1 ≤ M then B.phaseDriftTerm l P y else 0 := by
  by_cases hl : l - 1 ≤ M <;> simp [phaseDriftTerm, truncate, hl]

theorem truncate_tangentSecondTerm {ξ : Fin n → ℝ} {U : Set Y} (B : BoundaryLayerCoefficients ξ U)
    (M l d : ℕ) (P : Y → ℂ[X]) (y : Y) :
    (B.truncate M).tangentSecondTerm l d P y = if l - 2 ≤ M then B.tangentSecondTerm l d P y else 0 := by
  by_cases hl : l - 2 ≤ M <;> simp [tangentSecondTerm, truncate, hl]

theorem truncate_tangentFirstTerm {ξ : Fin n → ℝ} {U : Set Y} (B : BoundaryLayerCoefficients ξ U)
    (M l d : ℕ) (P : Y → ℂ[X]) (y : Y) :
    (B.truncate M).tangentFirstTerm l d P y = if l - 2 ≤ M then B.tangentFirstTerm l d P y else 0 := by
  by_cases hl : l - 2 ≤ M <;> simp [tangentFirstTerm, truncate, hl]

theorem forcing_gap_decomposition {ξ : Fin n → ℝ} {U : Set Y} (B : BoundaryLayerCoefficients ξ U)
    (M k l : ℕ) (P : Y → ℂ[X]) (y : Y) :
    (B.truncate M).forcing (k + l) k P y =
      (if l ≤ M then B.principalTerm l P y else 0) +
      (if l - 1 ≤ M then B.normalTerm l P y else 0) +
      (if l - 1 ≤ M then B.crossTerm l (2 * k) P y else 0) +
      (if l - 1 ≤ M then B.phaseDriftTerm l P y else 0) +
      (if 2 ≤ l then (if l - 2 ≤ M then B.tangentSecondTerm l (2 * k) P y else 0) +
        (if l - 2 ≤ M then B.tangentFirstTerm l (2 * k) P y else 0) else 0) := by
  simp only [forcing, Nat.add_sub_cancel_left, truncate_principalTerm, truncate_normalTerm,
    truncate_crossTerm, truncate_phaseDriftTerm, truncate_tangentSecondTerm, truncate_tangentFirstTerm]

end CalderonPatch.BoundaryLayer.BoundaryLayerCoefficients

open Polynomial Finset Set
namespace CalderonPatch.BoundaryLayer

theorem shifted_truncated_action_sum {K : Type*} [CommRing K]
    (M d : ℕ) (hd : d ≤ 2) (h : K) (F : ℕ → K) :
    (∑ l ∈ range (M + 3), if d ≤ l then h ^ l * (if l - d ≤ M then F l else 0) else 0) =
      h ^ d * ∑ m ∈ range (M + 1), h ^ m * F (m + d) := by
  have he := finite_shifted_power_sum M d hd h (fun m => F (m + d))
  calc
    _ = ∑ l ∈ range (M + 3), if d ≤ l then h ^ l *
        (if l - d ≤ M then F ((l - d) + d) else 0) else 0 := by
      apply sum_congr rfl
      intro l hl
      by_cases hdl : d ≤ l
      · simp only [if_pos hdl, Nat.sub_add_cancel hdl]
      · simp only [if_neg hdl]
    _ = _ := he

namespace BoundaryLayerCoefficients
variable {n : ℕ}
local notation "Y" => EuclideanSpace ℝ (Fin n)

theorem forcing_gap_power_sum {ξ : Fin n → ℝ} {U : Set Y} (B : BoundaryLayerCoefficients ξ U)
    (M k : ℕ) (P : Y → ℂ[X]) (y : Y) (H : ℂ[X]) :
    (∑ l ∈ range (M + 3), if 0 < l then H ^ l * (B.truncate M).forcing (k + l) k P y else 0) =
      ((∑ m ∈ range (M + 1), H ^ m * B.principalTerm m P y) - B.principalTerm 0 P y) +
      H * (∑ m ∈ range (M + 1), H ^ m * B.normalTerm (m + 1) P y) +
      H * (∑ m ∈ range (M + 1), H ^ m * B.crossTerm (m + 1) (2 * k) P y) +
      H * (∑ m ∈ range (M + 1), H ^ m * B.phaseDriftTerm (m + 1) P y) +
      H ^ 2 * (∑ m ∈ range (M + 1), H ^ m * B.tangentSecondTerm (m + 2) (2 * k) P y) +
      H ^ 2 * (∑ m ∈ range (M + 1), H ^ m * B.tangentFirstTerm (m + 2) (2 * k) P y) := by
  have hd (l : ℕ) : (if 0 < l then H ^ l * (B.truncate M).forcing (k + l) k P y else 0) =
      (if 0 < l then H ^ l * (if l ≤ M then B.principalTerm l P y else 0) else 0) +
      (if 1 ≤ l then H ^ l * (if l - 1 ≤ M then B.normalTerm l P y else 0) else 0) +
      (if 1 ≤ l then H ^ l * (if l - 1 ≤ M then B.crossTerm l (2 * k) P y else 0) else 0) +
      (if 1 ≤ l then H ^ l * (if l - 1 ≤ M then B.phaseDriftTerm l P y else 0) else 0) +
      (if 2 ≤ l then H ^ l * (if l - 2 ≤ M then B.tangentSecondTerm l (2 * k) P y else 0) else 0) +
      (if 2 ≤ l then H ^ l * (if l - 2 ≤ M then B.tangentFirstTerm l (2 * k) P y else 0) else 0) := by
    rw [B.forcing_gap_decomposition]
    by_cases hp : 0 < l
    · have h1 : 1 ≤ l := by omega
      by_cases h2 : 2 ≤ l
      · simp only [if_pos hp, if_pos h1, if_pos h2]
        ring
      · simp only [if_pos hp, if_pos h1, if_neg h2]
        ring
    · have h1 : ¬1 ≤ l := by omega
      have h2 : ¬2 ≤ l := by omega
      simp only [if_neg hp, if_neg h1, if_neg h2, add_zero]
  simp_rw [hd]
  rw [sum_add_distrib, sum_add_distrib, sum_add_distrib, sum_add_distrib, sum_add_distrib,
    positive_truncated_power_sum,
    shifted_truncated_action_sum M 1 (by omega),
    shifted_truncated_action_sum M 1 (by omega),
    shifted_truncated_action_sum M 1 (by omega),
    shifted_truncated_action_sum M 2 (by omega),
    shifted_truncated_action_sum M 2 (by omega)]
  simp only [pow_one]

end BoundaryLayerCoefficients
end CalderonPatch.BoundaryLayer
