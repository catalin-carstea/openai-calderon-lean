/-
Adapted from the conformal Poisson Lean formalization by Cătălin I. Cârstea,
Tony Liimatainen, Yi-Hsuan Lin, and William Trad, BSD 3-Clause.
Source: arxiv-2610.13592-lean commit 4cfcab036aedbb4f825a3aeb366da12fe5673ddd.
See the source and license in references/conformal-poisson-4cfcab03.
-/
module

public import Proof.CalderonPatch.BoundaryLayerResidual
public import Proof.CalderonPatch.BoundaryLayerScalar

public import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Normed.Lp.Matrix
import Mathlib.Tactic

public section

noncomputable section

open Polynomial Finset Set
namespace CalderonPatch.BoundaryLayer

theorem polynomialProfile_C_pow_mul (κ : ℝ) (c : ℂ) (m : ℕ) (p : ℂ[X]) (s : ℝ) :
    polynomialProfile κ ((C c) ^ m * p) s = c ^ m * polynomialProfile κ p s := by
  rw [← map_pow, polynomialProfile_C_mul]

namespace BoundaryLayerCoefficients
variable {n : ℕ}
local notation "Y" => EuclideanSpace ℝ (Fin n)

@[expose] def matrixTaylor {ξ : Fin n → ℝ} {U : Set Y} (B : BoundaryLayerCoefficients ξ U)
    (M : ℕ) (y : Y) (t : ℝ) : Matrix (Fin n) (Fin n) ℂ :=
  fun i j => ∑ m ∈ range (M + 1), (t : ℂ) ^ m * B.inverse m i j y

@[expose] def normalTaylor {ξ : Fin n → ℝ} {U : Set Y} (B : BoundaryLayerCoefficients ξ U)
    (M : ℕ) (y : Y) (t : ℝ) : ℂ :=
  ∑ m ∈ range (M + 1), (t : ℂ) ^ m * B.normalDrift m y

@[expose] def tangentTaylor {ξ : Fin n → ℝ} {U : Set Y} (B : BoundaryLayerCoefficients ξ U)
    (M : ℕ) (y : Y) (t : ℝ) (i : Fin n) : ℂ :=
  ∑ m ∈ range (M + 1), (t : ℂ) ^ m * B.tangentDrift m i y

theorem matrixTaylor_read {ξ : Fin n → ℝ} {U : Set Y} (B : BoundaryLayerCoefficients ξ U)
    (M : ℕ) (y : Y) (t : ℝ) (W : Fin n → Fin n → ℂ) :
    (∑ i, ∑ j, B.matrixTaylor M y t i j * W i j) =
      ∑ m ∈ range (M + 1), (t : ℂ) ^ m * ∑ i, ∑ j, B.inverse m i j y * W i j := by
  unfold matrixTaylor
  simp only [sum_mul]
  calc
    _ = ∑ i, ∑ m ∈ range (M + 1), ∑ j, ((t : ℂ) ^ m * B.inverse m i j y) * W i j := by
      apply sum_congr rfl
      intro i hi
      exact sum_comm
    _ = ∑ m ∈ range (M + 1), ∑ i, ∑ j, ((t : ℂ) ^ m * B.inverse m i j y) * W i j := sum_comm
    _ = _ := by simp only [mul_sum, mul_assoc]

theorem tangentTaylor_read {ξ : Fin n → ℝ} {U : Set Y} (B : BoundaryLayerCoefficients ξ U)
    (M : ℕ) (y : Y) (t : ℝ) (W : Fin n → ℂ) :
    (∑ i, B.tangentTaylor M y t i * W i) =
      ∑ m ∈ range (M + 1), (t : ℂ) ^ m * ∑ i, B.tangentDrift m i y * W i := by
  unfold tangentTaylor
  simp only [sum_mul]
  rw [sum_comm]
  simp only [mul_sum, mul_assoc]

theorem matrixTaylor_symmetric {ξ : Fin n → ℝ} {U : Set Y} (B : BoundaryLayerCoefficients ξ U)
    (M : ℕ) {y : Y} (hy : y ∈ U) (t : ℝ) (i j : Fin n) :
    B.matrixTaylor M y t i j = B.matrixTaylor M y t j i := by
  apply sum_congr rfl
  intro m hm
  rw [B.inverse_symm m i j y hy]

end BoundaryLayerCoefficients
end CalderonPatch.BoundaryLayer

open Polynomial Finset Set
open scoped ContDiff
namespace CalderonPatch.BoundaryLayer.BoundaryLayerCoefficients
variable {n : ℕ}
local notation "Y" => EuclideanSpace ℝ (Fin n)
local notation "e" => EuclideanSpace.basisFun (Fin n) ℝ

theorem principalTaylor_profile {ξ : Fin n → ℝ} {U : Set Y} (B : BoundaryLayerCoefficients ξ U)
    (M : ℕ) (P : Y → ℂ[X]) (y : Y) (h s : ℝ) :
    polynomialProfile (B.kappa y) (∑ m ∈ range (M + 1), (C (h : ℂ)) ^ m * B.principalTerm m P y) s =
      (∑ i, ∑ j, B.matrixTaylor M y (h * s) i j * (ξ i : ℂ) * (ξ j : ℂ)) *
        polynomialProfile (B.kappa y) (P y) s := by
  have he := B.matrixTaylor_read M y (h * s) (fun i j => (ξ i : ℂ) * (ξ j : ℂ))
  simp only [← mul_assoc] at he
  rw [he, sum_mul, polynomialProfile_sum]
  apply sum_congr rfl
  intro m hm
  rw [polynomialProfile_C_pow_mul, B.principalTerm_read]
  simp only [Complex.ofReal_mul, mul_pow]
  ring

theorem normalTaylor_profile {ξ : Fin n → ℝ} {U : Set Y} (B : BoundaryLayerCoefficients ξ U)
    (M : ℕ) (P : Y → ℂ[X]) (y : Y) (h s : ℝ) :
    polynomialProfile (B.kappa y) (∑ m ∈ range (M + 1), (C (h : ℂ)) ^ m * B.normalTerm (m + 1) P y) s =
      B.normalTaylor M y (h * s) / 2 * deriv (polynomialProfile (B.kappa y) (P y)) s := by
  unfold normalTaylor
  rw [sum_div, sum_mul, polynomialProfile_sum]
  apply sum_congr rfl
  intro m hm
  rw [polynomialProfile_C_pow_mul, B.normalTerm_read]
  simp only [Nat.add_sub_cancel, Complex.ofReal_mul, mul_pow]
  ring

theorem crossTaylor_profile {ξ : Fin n → ℝ} {U : Set Y} (B : BoundaryLayerCoefficients ξ U)
    (hU : IsOpen U) (M d : ℕ) {P : Y → ℂ[X]} (hP : CoeffContDiffOn P U)
    (hD : ∀ y ∈ U, (P y).natDegree ≤ d) {y : Y} (hy : y ∈ U) (h s : ℝ) :
    polynomialProfile (B.kappa y) (∑ m ∈ range (M + 1), (C (h : ℂ)) ^ m * B.crossTerm (m + 1) d P y) s =
      (-2 * Complex.I) * ∑ i, ∑ j, B.matrixTaylor M y (h * s) i j * (ξ i : ℂ) *
        fderiv ℝ (fun x => polynomialProfile (B.kappa x) (P x) s) y (e j) := by
  have he := B.matrixTaylor_read M y (h * s)
    (fun i j => (ξ i : ℂ) * fderiv ℝ (fun x => polynomialProfile (B.kappa x) (P x) s) y (e j))
  simp only [← mul_assoc] at he
  rw [he, polynomialProfile_sum]
  simp_rw [polynomialProfile_C_pow_mul, B.crossTerm_read hU _ d hP hD hy s]
  simp only [Nat.add_sub_cancel, Complex.ofReal_mul, mul_pow, mul_sum]
  apply sum_congr rfl
  intro m hm
  apply sum_congr rfl
  intro i hi
  apply sum_congr rfl
  intro j hj
  ring

theorem phaseTaylor_profile {ξ : Fin n → ℝ} {U : Set Y} (B : BoundaryLayerCoefficients ξ U)
    (M : ℕ) (P : Y → ℂ[X]) (y : Y) (h s : ℝ) :
    polynomialProfile (B.kappa y) (∑ m ∈ range (M + 1), (C (h : ℂ)) ^ m * B.phaseDriftTerm (m + 1) P y) s =
      (-Complex.I) * ∑ i, B.tangentTaylor M y (h * s) i * (ξ i : ℂ) * polynomialProfile (B.kappa y) (P y) s := by
  have he := B.tangentTaylor_read M y (h * s)
    (fun i => (ξ i : ℂ) * polynomialProfile (B.kappa y) (P y) s)
  simp only [← mul_assoc] at he
  rw [he, polynomialProfile_sum]
  simp_rw [polynomialProfile_C_pow_mul, B.phaseDriftTerm_read]
  simp only [Nat.add_sub_cancel, Complex.ofReal_mul, mul_pow, mul_sum]
  apply sum_congr rfl
  intro m hm
  apply sum_congr rfl
  intro i hi
  ring

theorem tangentSecondTaylor_profile {ξ : Fin n → ℝ} {U : Set Y} (B : BoundaryLayerCoefficients ξ U)
    (hU : IsOpen U) (M d : ℕ) {P : Y → ℂ[X]} (hP : CoeffContDiffOn P U)
    (hD : ∀ y ∈ U, (P y).natDegree ≤ d) {y : Y} (hy : y ∈ U) (h s : ℝ) :
    polynomialProfile (B.kappa y) (∑ m ∈ range (M + 1), (C (h : ℂ)) ^ m * B.tangentSecondTerm (m + 2) d P y) s =
      -(∑ i, ∑ j, B.matrixTaylor M y (h * s) i j *
        fderiv ℝ (fun x => fderiv ℝ (fun z => polynomialProfile (B.kappa z) (P z) s) x (e j)) y (e i)) := by
  have he := B.matrixTaylor_read M y (h * s)
    (fun i j => fderiv ℝ (fun x => fderiv ℝ (fun z => polynomialProfile (B.kappa z) (P z) s) x (e j)) y (e i))
  rw [he, polynomialProfile_sum]
  simp_rw [polynomialProfile_C_pow_mul, B.tangentSecondTerm_read hU _ d hP hD hy s]
  simp only [Nat.add_sub_cancel, Complex.ofReal_mul, mul_pow, mul_sum, mul_neg, ← sum_neg_distrib]
  apply sum_congr rfl
  intro m hm
  apply sum_congr rfl
  intro i hi
  apply sum_congr rfl
  intro j hj
  ring

theorem tangentFirstTaylor_profile {ξ : Fin n → ℝ} {U : Set Y} (B : BoundaryLayerCoefficients ξ U)
    (hU : IsOpen U) (M d : ℕ) {P : Y → ℂ[X]} (hP : CoeffContDiffOn P U)
    (hD : ∀ y ∈ U, (P y).natDegree ≤ d) {y : Y} (hy : y ∈ U) (h s : ℝ) :
    polynomialProfile (B.kappa y) (∑ m ∈ range (M + 1), (C (h : ℂ)) ^ m * B.tangentFirstTerm (m + 2) d P y) s =
      -(∑ i, B.tangentTaylor M y (h * s) i *
        fderiv ℝ (fun x => polynomialProfile (B.kappa x) (P x) s) y (e i)) := by
  have he := B.tangentTaylor_read M y (h * s)
    (fun i => fderiv ℝ (fun x => polynomialProfile (B.kappa x) (P x) s) y (e i))
  rw [he, polynomialProfile_sum]
  simp_rw [polynomialProfile_C_pow_mul, B.tangentFirstTerm_read hU _ d hP hD hy s]
  simp only [Nat.add_sub_cancel, Complex.ofReal_mul, mul_pow, mul_sum, mul_neg, ← sum_neg_distrib]
  apply sum_congr rfl
  intro m hm
  apply sum_congr rfl
  intro i hi
  ring

end CalderonPatch.BoundaryLayer.BoundaryLayerCoefficients

open Polynomial Finset Set
open scoped ContDiff
namespace CalderonPatch.BoundaryLayer

theorem polynomialProfile_sub (κ : ℝ) (p q : ℂ[X]) (s : ℝ) :
    polynomialProfile κ (p - q) s = polynomialProfile κ p s - polynomialProfile κ q s := by
  simp [polynomialProfile, smul_sub]

theorem polynomialProfile_zero (κ s : ℝ) : polynomialProfile κ 0 s = 0 := by
  simp [polynomialProfile]

namespace BoundaryLayerCoefficients
variable {n : ℕ}
local notation "Y" => EuclideanSpace ℝ (Fin n)

theorem principalTerm_zero_profile {ξ : Fin n → ℝ} {U : Set Y} (B : BoundaryLayerCoefficients ξ U)
    (P : Y → ℂ[X]) {y : Y} (hy : y ∈ U) (s : ℝ) :
    polynomialProfile (B.kappa y) (B.principalTerm 0 P y) s =
      B.kappa y ^ 2 • polynomialProfile (B.kappa y) (P y) s := by
  rw [B.principalTerm_read, pow_zero, mul_one, ← B.principal_squared y hy]
  simp only [Complex.real_smul, Complex.ofReal_pow]

theorem conjugatedTaylor_profile {ξ : Fin n → ℝ} {U : Set Y} (B : BoundaryLayerCoefficients ξ U)
    (hU : IsOpen U) (M k : ℕ) {P : Y → ℂ[X]} (hP : CoeffContDiffOn P U)
    (hD : ∀ y ∈ U, (P y).natDegree ≤ 2 * k) {y : Y} (hy : y ∈ U) (h s : ℝ) :
    conjugatedSplitOperator (B.matrixTaylor M y (h * s)) (B.normalTaylor M y (h * s))
      (B.tangentTaylor M y (h * s)) ξ h
      (fun x : Y × ℝ => polynomialProfile (B.kappa x.1) (P x.1) x.2) y s =
    polynomialProfile (B.kappa y)
      (C (2 * (B.kappa y : ℂ)) * derivative (P y) - derivative (derivative (P y))) s +
      ∑ l ∈ range (M + 3), if 0 < l then (h ^ l : ℂ) *
        polynomialProfile (B.kappa y) ((B.truncate M).forcing (k + l) k P y) s else 0 := by
  have hgap : (∑ l ∈ range (M + 3), if 0 < l then (h ^ l : ℂ) *
      polynomialProfile (B.kappa y) ((B.truncate M).forcing (k + l) k P y) s else 0) =
      polynomialProfile (B.kappa y) (∑ l ∈ range (M + 3), if 0 < l then
        (C (h : ℂ)) ^ l * (B.truncate M).forcing (k + l) k P y else 0) s := by
    rw [polynomialProfile_sum]
    apply sum_congr rfl
    intro l hl
    by_cases hpos : 0 < l
    · simp only [if_pos hpos, polynomialProfile_C_pow_mul, Complex.ofReal_pow]
    · simp only [if_neg hpos, polynomialProfile_zero]
  rw [hgap, B.forcing_gap_power_sum, ← secondOrder_polynomialProfile (B.kappa y) (P y) s]
  simp only [polynomialProfile_add, polynomialProfile_sub, polynomialProfile_C_mul,
    polynomialProfile_C_pow_mul]
  rw [B.principalTaylor_profile, B.normalTaylor_profile,
    B.crossTaylor_profile hU M (2 * k) hP hD hy,
    B.phaseTaylor_profile, B.tangentSecondTaylor_profile hU M (2 * k) hP hD hy,
    B.tangentFirstTaylor_profile hU M (2 * k) hP hD hy,
    B.principalTerm_zero_profile P hy]
  unfold conjugatedSplitOperator splitNormalSecond splitNormal splitFirst splitSecond
  simp only [Complex.real_smul]
  ring

end BoundaryLayerCoefficients
end CalderonPatch.BoundaryLayer

open Polynomial Finset Set
open scoped ContDiff
namespace CalderonPatch.BoundaryLayer.BoundaryLayerCoefficients
variable {n : ℕ}
local notation "Y" => EuclideanSpace ℝ (Fin n)

theorem finiteResidualProfile_eq_TaylorOperator_sum {ξ : Fin n → ℝ} {U : Set Y} (B : BoundaryLayerCoefficients ξ U)
    (hU : IsOpen U) {K : Set Y} (hK : IsClosed K) (a : Y → ℂ)
    (ha : ContDiffOn ℝ ∞ a U) (ha0 : ∀ y ∉ K, a y = 0)
    (M : ℕ) {y : Y} (hy : y ∈ U) (h s : ℝ) :
    B.finiteResidualProfile a M h (y, s) = ∑ k ∈ range (M + 1), (h ^ k : ℂ) *
      conjugatedSplitOperator (B.matrixTaylor M y (h * s)) (B.normalTaylor M y (h * s))
        (B.tangentTaylor M y (h * s)) ξ h (B.profile a k) y s := by
  have hk (k : ℕ) :
      conjugatedSplitOperator (B.matrixTaylor M y (h * s)) (B.normalTaylor M y (h * s))
        (B.tangentTaylor M y (h * s)) ξ h (B.profile a k) y s =
      polynomialProfile (B.kappa y)
        (C (2 * (B.kappa y : ℂ)) * derivative (B.layerPolynomial a k y) -
          derivative (derivative (B.layerPolynomial a k y))) s +
        ∑ l ∈ range (M + 3), if 0 < l then (h ^ l : ℂ) * polynomialProfile (B.kappa y)
          ((B.truncate M).forcing (k + l) k (B.layerPolynomial a k) y) s else 0 :=
    B.conjugatedTaylor_profile hU M k
      (B.layerPolynomial_properties hU hK a ha ha0 k).1
      (B.layerPolynomial_properties hU hK a ha ha0 k).2.1 hy h s
  rw [B.finiteResidualProfile_eq_double_sum]
  simp_rw [hk]
  simp only [mul_add, mul_sum, sum_add_distrib, Complex.ofReal_pow, pow_add, mul_ite, mul_zero, mul_assoc]

end CalderonPatch.BoundaryLayer.BoundaryLayerCoefficients

open Set Metric Filter Topology
open scoped ContDiff
namespace CalderonPatch.BoundaryLayer

theorem cutoff_deriv_zero_inner (η : ContDiffBump (0 : ℝ)) {t : ℝ} (ht : t ∈ ball 0 η.rIn) :
    deriv η t = 0 := by
  exact (η.eventuallyEq_one_of_mem_ball ht).deriv_eq.trans ((hasDerivAt_const t (1 : ℝ)).deriv)

theorem cutoff_second_deriv_zero_inner (η : ContDiffBump (0 : ℝ)) {t : ℝ} (ht : t ∈ ball 0 η.rIn) :
    deriv (deriv η) t = 0 := by
  have he : deriv η =ᶠ[𝓝 t] fun _ => (0 : ℝ) := by
    filter_upwards [isOpen_ball.mem_nhds ht] with r hr
    exact cutoff_deriv_zero_inner η hr
  simpa only [deriv_const] using he.deriv_eq

theorem cutoff_derivative_physical_distance (η : ContDiffBump (0 : ℝ)) {t : ℝ} (ht : 0 ≤ t)
    (hD : deriv η t ≠ 0 ∨ deriv (deriv η) t ≠ 0) : η.rIn ≤ t := by
  by_contra hn
  have hi : t ∈ ball (0 : ℝ) η.rIn := by
    simpa only [mem_ball, Real.dist_eq, sub_zero, abs_of_nonneg ht] using lt_of_not_ge hn
  rcases hD with hD | hD
  · exact hD (cutoff_deriv_zero_inner η hi)
  · exact hD (cutoff_second_deriv_zero_inner η hi)

theorem exists_cutoff_two_jet_bound (η : ContDiffBump (0 : ℝ)) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ t : ℝ, |η t| ≤ B ∧ |deriv η t| ≤ B ∧ |deriv (deriv η) t| ≤ B := by
  have hη : ContDiff ℝ ∞ η := η.contDiff
  have hd : ContDiff ℝ ∞ (deriv η) := hη.deriv'
  have hdd : ContDiff ℝ ∞ (deriv (deriv η)) := hd.deriv'
  obtain ⟨C₁, hC₁⟩ := η.hasCompactSupport.deriv.exists_bound_of_continuous hd.continuous
  obtain ⟨C₂, hC₂⟩ := η.hasCompactSupport.deriv.deriv.exists_bound_of_continuous hdd.continuous
  let B : ℝ := 1 + max 0 C₁ + max 0 C₂
  have h0₁ : 0 ≤ max 0 C₁ := le_max_left _ _
  have h0₂ : 0 ≤ max 0 C₂ := le_max_left _ _
  refine ⟨B, by dsimp [B]; linarith, ?_⟩
  intro t
  have hv : |η t| ≤ 1 := by rw [abs_of_nonneg η.nonneg]; exact η.le_one
  have hdv : |deriv η t| ≤ C₁ := by simpa only [Real.norm_eq_abs] using hC₁ t
  have hddv : |deriv (deriv η) t| ≤ C₂ := by simpa only [Real.norm_eq_abs] using hC₂ t
  dsimp [B]
  exact ⟨hv.trans (by linarith), hdv.trans (by have hh := le_max_right 0 C₁; linarith),
    hddv.trans (by have hh := le_max_right 0 C₂; linarith)⟩

end CalderonPatch.BoundaryLayer

open Set Finset
open scoped ContDiff
namespace CalderonPatch.BoundaryLayer
variable {n : ℕ}
local notation "Y" => EuclideanSpace ℝ (Fin n)
local notation "e" => EuclideanSpace.basisFun (Fin n) ℝ

@[expose] def normalCutoffWave (η : ℝ → ℝ) (W : Y × ℝ → ℂ) (x : Y × ℝ) : ℂ :=
  (η x.2 : ℂ) * W x

theorem contDiff_normalCutoffWave {η : ℝ → ℝ} (hη : ContDiff ℝ ∞ η)
    {W : Y × ℝ → ℂ} (hW : ContDiff ℝ ∞ W) : ContDiff ℝ ∞ (normalCutoffWave η W) :=
  (Complex.ofRealCLM.contDiff.comp (hη.comp contDiff_snd)).mul hW

theorem deriv_realCutoff_mul {η : ℝ → ℝ} (hη : ContDiff ℝ ∞ η)
    {f : ℝ → ℂ} (hf : ContDiff ℝ ∞ f) (t : ℝ) :
    deriv (fun r => (η r : ℂ) * f r) t = ((deriv η t : ℝ) : ℂ) * f t + (η t : ℂ) * deriv f t := by
  exact (((hη.differentiable (by decide) t).hasDerivAt.ofReal_comp).mul
    (hf.differentiable (by decide) t).hasDerivAt).deriv

theorem deriv_twice_realCutoff_mul {η : ℝ → ℝ} (hη : ContDiff ℝ ∞ η)
    {f : ℝ → ℂ} (hf : ContDiff ℝ ∞ f) (t : ℝ) :
    deriv (deriv (fun r => (η r : ℂ) * f r)) t =
      ((deriv (deriv η) t : ℝ) : ℂ) * f t + 2 * ((deriv η t : ℝ) : ℂ) * deriv f t +
        (η t : ℂ) * deriv (deriv f) t := by
  have he : deriv (fun r => (η r : ℂ) * f r) =
      fun r => ((deriv η r : ℝ) : ℂ) * f r + (η r : ℂ) * deriv f r :=
    funext (fun r => deriv_realCutoff_mul hη hf r)
  have hdη : ContDiff ℝ ∞ (deriv η) := hη.deriv'
  have hdf : ContDiff ℝ ∞ (deriv f) := hf.deriv'
  have h₁ := (((hdη.differentiable (by decide) t).hasDerivAt.ofReal_comp).mul
    (hf.differentiable (by decide) t).hasDerivAt)
  have h₂ := (((hη.differentiable (by decide) t).hasDerivAt.ofReal_comp).mul
    (hdf.differentiable (by decide) t).hasDerivAt)
  rw [he]
  calc
    _ = _ := (h₁.add h₂).deriv
    _ = _ := by ring

theorem splitNormal_normalCutoffWave {η : ℝ → ℝ} (hη : ContDiff ℝ ∞ η)
    {W : Y × ℝ → ℂ} (hW : ContDiff ℝ ∞ W) (y : Y) (t : ℝ) :
    splitNormal (normalCutoffWave η W) y t =
      ((deriv η t : ℝ) : ℂ) * W (y, t) + (η t : ℂ) * splitNormal W y t :=
  deriv_realCutoff_mul hη (hW.comp (contDiff_const.prodMk contDiff_id)) t

theorem splitNormalSecond_normalCutoffWave {η : ℝ → ℝ} (hη : ContDiff ℝ ∞ η)
    {W : Y × ℝ → ℂ} (hW : ContDiff ℝ ∞ W) (y : Y) (t : ℝ) :
    splitNormalSecond (normalCutoffWave η W) y t =
      ((deriv (deriv η) t : ℝ) : ℂ) * W (y, t) + 2 * ((deriv η t : ℝ) : ℂ) * splitNormal W y t +
        (η t : ℂ) * splitNormalSecond W y t :=
  deriv_twice_realCutoff_mul hη (hW.comp (contDiff_const.prodMk contDiff_id)) t

theorem splitFirst_normalCutoffWave (η : ℝ → ℝ)
    {W : Y × ℝ → ℂ} (hW : ContDiff ℝ ∞ W) (y : Y) (t : ℝ) (i : Fin n) :
    splitFirst (normalCutoffWave η W) y t i = (η t : ℂ) * splitFirst W y t i := by
  have hs : ContDiff ℝ ∞ (fun z : Y => W (z, t)) := hW.comp (contDiff_id.prodMk contDiff_const)
  unfold splitFirst normalCutoffWave
  dsimp only [Prod.snd]
  rw [fderiv_const_mul (hs.differentiable (by decide) y)]
  rfl

private theorem directional_fderiv_contDiff {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : E → F} (hf : ContDiff ℝ ∞ f) (v : E) :
    ContDiff ℝ ∞ (fun x => fderiv ℝ f x v) :=
  (hf.fderiv_right (by simp : (∞ : ℕ∞ω) + 1 ≤ ∞)).clm_apply contDiff_const

theorem splitSecond_normalCutoffWave (η : ℝ → ℝ)
    {W : Y × ℝ → ℂ} (hW : ContDiff ℝ ∞ W) (y : Y) (t : ℝ) (i j : Fin n) :
    splitSecond (normalCutoffWave η W) y t i j = (η t : ℂ) * splitSecond W y t i j := by
  have hs : ContDiff ℝ ∞ (fun z : Y => W (z, t)) := hW.comp (contDiff_id.prodMk contDiff_const)
  have he : (fun z : Y => splitFirst (normalCutoffWave η W) z t j) =
      fun z => (η t : ℂ) * splitFirst W z t j :=
    funext (fun z => splitFirst_normalCutoffWave η hW z t j)
  change fderiv ℝ (fun z => splitFirst (normalCutoffWave η W) z t j) y (e i) = _
  rw [he]
  have hd : ContDiff ℝ ∞ (fun z => splitFirst W z t j) := directional_fderiv_contDiff hs (e j)
  rw [fderiv_const_mul (hd.differentiable (by decide) y)]
  rfl

theorem complexSplitOperator_normalCutoffWave (A : Matrix (Fin n) (Fin n) ℂ) (τ : ℂ) (c : Fin n → ℂ)
    {η : ℝ → ℝ} (hη : ContDiff ℝ ∞ η)
    {W : Y × ℝ → ℂ} (hW : ContDiff ℝ ∞ W) (y : Y) (t : ℝ) :
    complexSplitOperator A τ c (normalCutoffWave η W) y t =
      (η t : ℂ) * complexSplitOperator A τ c W y t +
        (-((deriv (deriv η) t : ℝ) : ℂ) + τ / 2 * ((deriv η t : ℝ) : ℂ)) * W (y, t) -
        2 * ((deriv η t : ℝ) : ℂ) * splitNormal W y t := by
  have h₂ : (∑ i, ∑ j, A i j * splitSecond (normalCutoffWave η W) y t i j) =
      (η t : ℂ) * ∑ i, ∑ j, A i j * splitSecond W y t i j := by
    simp only [mul_sum]
    apply sum_congr rfl; intro i hi
    apply sum_congr rfl; intro j hj
    rw [splitSecond_normalCutoffWave η hW]
    ring
  have h₁ : (∑ i, c i * splitFirst (normalCutoffWave η W) y t i) =
      (η t : ℂ) * ∑ i, c i * splitFirst W y t i := by
    rw [mul_sum]
    apply sum_congr rfl; intro i hi
    rw [splitFirst_normalCutoffWave η hW]
    ring
  unfold complexSplitOperator
  rw [splitNormalSecond_normalCutoffWave hη hW, splitNormal_normalCutoffWave hη hW, h₂, h₁]
  ring

end CalderonPatch.BoundaryLayer

open Set Finset
open scoped ContDiff
namespace CalderonPatch.BoundaryLayer
variable {n : ℕ}
local notation "Y" => EuclideanSpace ℝ (Fin n)

theorem contDiff_scaledPlaneWave (ξ : Fin n → ℝ) (h : ℝ)
    {V : Y × ℝ → ℂ} (hV : ContDiff ℝ ∞ V) : ContDiff ℝ ∞ (scaledPlaneWave ξ h V) := by
  have hm : ContDiff ℝ ∞ (fun x : Y × ℝ => (x.1, x.2 / h)) :=
    contDiff_fst.prodMk (contDiff_snd.div_const h)
  exact ((tangentialWave_contDiff ξ h).comp contDiff_fst).mul (hV.comp hm)

def scaledCutoffDefect (τ : ℂ) (η : ℝ → ℝ) (h : ℝ)
    (V : Y × ℝ → ℂ) (y : Y) (t : ℝ) : ℂ :=
  (h : ℂ) ^ 2 * (-((deriv (deriv η) t : ℝ) : ℂ) + τ / 2 * ((deriv η t : ℝ) : ℂ)) * V (y, t / h) -
    2 * (h : ℂ) * ((deriv η t : ℝ) : ℂ) * splitNormal V y (t / h)

theorem complexSplitOperator_scaledCutoff (A : Matrix (Fin n) (Fin n) ℂ)
    (hA : ∀ i j, A i j = A j i) (τ : ℂ) (c : Fin n → ℂ) (ξ : Fin n → ℝ)
    {η : ℝ → ℝ} (hη : ContDiff ℝ ∞ η) {h : ℝ} (hh : h ≠ 0)
    {V : Y × ℝ → ℂ} (hV : ContDiff ℝ ∞ V) (y : Y) (t : ℝ) :
    (h : ℂ) ^ 2 * complexSplitOperator A τ c (normalCutoffWave η (scaledPlaneWave ξ h V)) y t =
      tangentialWave ξ h y * ((η t : ℂ) * conjugatedSplitOperator A τ c ξ h V y (t / h) +
        scaledCutoffDefect τ η h V y t) := by
  rw [complexSplitOperator_normalCutoffWave A τ c hη (contDiff_scaledPlaneWave ξ h hV)]
  have hL := complexSplitOperator_scaledPlaneWave A hA τ c ξ hh hV y t
  have hN := splitNormal_scaledPlaneWave ξ h hV y t
  rw [mul_sub, mul_add]
  have hmain : (h : ℂ) ^ 2 * ((η t : ℂ) * complexSplitOperator A τ c (scaledPlaneWave ξ h V) y t) =
      tangentialWave ξ h y * ((η t : ℂ) * conjugatedSplitOperator A τ c ξ h V y (t / h)) := by
    calc
      _ = (η t : ℂ) * ((h : ℂ) ^ 2 * complexSplitOperator A τ c (scaledPlaneWave ξ h V) y t) := by ring
      _ = _ := by rw [hL]; ring
  rw [hmain, hN]
  unfold scaledCutoffDefect scaledPlaneWave
  have hh' : (h : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hh
  field_simp
  all_goals ring

end CalderonPatch.BoundaryLayer

open Set Finset
open scoped ContDiff
namespace CalderonPatch.BoundaryLayer
variable {n : ℕ}
local notation "Y" => EuclideanSpace ℝ (Fin n)

theorem norm_exp_tail_bound {C c δ t h : ℝ} {v : ℂ}
    (hC : 0 ≤ C) (hc : 0 < c) (hδ : 0 < δ) (hh : 0 < h) (ht : δ ≤ t)
    (hv : ‖v‖ ≤ C * Real.exp (-c * (t / h))) (N : ℕ) :
    ‖v‖ ≤ (C * (N.factorial : ℝ) / (c * δ) ^ N) * h ^ N := by
  have he : Real.exp (-c * (t / h)) ≤ Real.exp (-(c * δ) / h) := by
    apply Real.exp_le_exp.mpr
    have hd := div_le_div_of_nonneg_right ht hh.le
    calc
      -c * (t / h) ≤ -c * (δ / h) := mul_le_mul_of_nonpos_left hd (by linarith)
      _ = _ := by ring
  calc
    _ ≤ C * Real.exp (-(c * δ) / h) := hv.trans (mul_le_mul_of_nonneg_left he hC)
    _ ≤ C * ((N.factorial : ℝ) / (c * δ) ^ N * h ^ N) :=
      mul_le_mul_of_nonneg_left (exp_neg_div_le_mul_pow (mul_pos hc hδ) hh N) hC
    _ = _ := by ring

theorem scaledCutoffDefect_bound {τ : ℂ} {η : ℝ → ℝ} {h B T J : ℝ}
    (hh : 0 ≤ h) (hh1 : h ≤ 1) (hB : 0 ≤ B) (hT : 0 ≤ T) (hJ : 0 ≤ J)
    (hτ : ‖τ‖ ≤ T) (V : Y × ℝ → ℂ) (y : Y) (t : ℝ)
    (hd : |deriv η t| ≤ B) (hdd : |deriv (deriv η) t| ≤ B)
    (hv : ‖V (y, t / h)‖ ≤ J) (hn : ‖splitNormal V y (t / h)‖ ≤ J) :
    ‖scaledCutoffDefect τ η h V y t‖ ≤ (B + T / 2 * B + 2 * B) * J := by
  have hhC : ‖(h : ℂ)‖ ≤ 1 := by simpa only [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hh] using hh1
  have hh2 : ‖(h : ℂ) ^ 2‖ ≤ 1 := by simpa only [norm_pow, one_pow] using pow_le_one₀ (n := 2) (norm_nonneg (h : ℂ)) hhC
  have hηd : ‖((deriv η t : ℝ) : ℂ)‖ ≤ B := by simpa only [Complex.norm_real, Real.norm_eq_abs] using hd
  have hηdd : ‖((deriv (deriv η) t : ℝ) : ℂ)‖ ≤ B := by simpa only [Complex.norm_real, Real.norm_eq_abs] using hdd
  have ha : ‖-((deriv (deriv η) t : ℝ) : ℂ) + τ / 2 * ((deriv η t : ℝ) : ℂ)‖ ≤ B + T / 2 * B := by
    apply (norm_add_le _ _).trans
    rw [norm_neg, norm_mul, norm_div, Complex.norm_ofNat]
    gcongr
  unfold scaledCutoffDefect
  calc
    _ ≤ ‖(h : ℂ) ^ 2 * (-((deriv (deriv η) t : ℝ) : ℂ) + τ / 2 * ((deriv η t : ℝ) : ℂ)) * V (y, t / h)‖ +
      ‖2 * (h : ℂ) * ((deriv η t : ℝ) : ℂ) * splitNormal V y (t / h)‖ := norm_sub_le _ _
    _ ≤ 1 * (B + T / 2 * B) * J + (2 * 1 * B) * J := by
      simp only [norm_mul, Complex.norm_ofNat]
      apply add_le_add
      · exact mul_le_mul (mul_le_mul hh2 ha (norm_nonneg _) (by positivity)) hv (norm_nonneg _) (by positivity)
      · gcongr
    _ = _ := by ring

namespace BoundaryLayerCoefficients

theorem exists_cutoff_defect_bound {ξ : Fin n → ℝ} {U : Set Y} (B : BoundaryLayerCoefficients ξ U)
    (hU : IsOpen U) {K : Set Y} (hK : IsCompact K) (hKU : K ⊆ U)
    (a : Y → ℂ) (ha : ContDiffOn ℝ ∞ a U) (ha0 : ∀ y ∉ K, a y = 0)
    (η : ContDiffBump (0 : ℝ)) {T : ℝ} (hT : 0 ≤ T) (M N : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ j : ℕ, j ≤ M → ∀ y ∈ K, ∀ t : ℝ, 0 ≤ t →
      ∀ h : ℝ, 0 < h → h ≤ 1 → ∀ τ : ℂ, ‖τ‖ ≤ T →
      ‖scaledCutoffDefect τ η h (B.profile a j) y t‖ ≤ C * h ^ N := by
  obtain ⟨c, J, hc, hJ, hb⟩ := B.exists_uniform_actual_layerJet_moment_exp_bound hU hK hKU a ha ha0 M 0
  obtain ⟨D, hD, hDb⟩ := exists_cutoff_two_jet_bound η
  let Q : ℝ := J * (N.factorial : ℝ) / (c * η.rIn) ^ N
  have hQ : 0 ≤ Q := div_nonneg (mul_nonneg hJ (Nat.cast_nonneg _)) (pow_nonneg (mul_pos hc η.rIn_pos).le N)
  let W : ℝ := D + T / 2 * D + 2 * D
  have hW : 0 ≤ W := by dsimp [W]; positivity
  refine ⟨W * Q, mul_nonneg hW hQ, ?_⟩
  intro j hj y hy t ht h hh hh1 τ hτ
  by_cases hzero : deriv η t = 0 ∧ deriv (deriv η) t = 0
  · simp only [scaledCutoffDefect, hzero.1, hzero.2, Complex.ofReal_zero, neg_zero, mul_zero, zero_add, add_zero,
      zero_mul, sub_zero, norm_zero]
    positivity
  · have haway : η.rIn ≤ t := cutoff_derivative_physical_distance η ht (by tauto)
    obtain ⟨hv, hn, hd, hdd⟩ := hb j hj y hy (t / h) (div_nonneg ht hh.le)
    simp only [pow_zero, one_mul] at hv hn
    have hv' := norm_exp_tail_bound hJ hc η.rIn_pos hh haway hv N
    have hn' := norm_exp_tail_bound hJ hc η.rIn_pos hh haway hn N
    have he := scaledCutoffDefect_bound hh.le hh1 hD hT (mul_nonneg hQ (pow_nonneg hh.le N))
      hτ (B.profile a j) y t (hDb t).2.1 (hDb t).2.2 hv' hn'
    exact he.trans_eq (by dsimp [W]; ring)

end BoundaryLayerCoefficients
end CalderonPatch.BoundaryLayer
