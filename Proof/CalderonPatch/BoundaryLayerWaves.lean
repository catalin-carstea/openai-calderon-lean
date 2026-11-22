/-
Adapted from the conformal Poisson Lean formalization by Cătălin I. Cârstea,
Tony Liimatainen, Yi-Hsuan Lin, and William Trad, BSD 3-Clause.
Source: arxiv-2610.13592-lean commit 4cfcab036aedbb4f825a3aeb366da12fe5673ddd.
See the source and license in references/conformal-poisson-4cfcab03.
-/
module

public import Proof.CalderonPatch.BoundaryLayerProfiles

import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Tactic

public section

noncomputable section

open Polynomial Set Finset
open scoped ContDiff
namespace CalderonPatch.BoundaryLayer

def profileBound (c : ℝ) (D : ℕ) (b : ℕ → ℝ) : ℝ :=
  ∑ j ∈ range D, b j * (j.factorial : ℝ) / c ^ j

theorem profileBound_nonneg {c : ℝ} (hc : 0 < c) (D : ℕ) {b : ℕ → ℝ}
    (hb : ∀ j, 0 ≤ b j) : 0 ≤ profileBound c D b :=
  sum_nonneg (fun j _ => div_nonneg (mul_nonneg (hb j) (Nat.cast_nonneg _)) (pow_nonneg hc.le _))

theorem norm_polynomialProfile_le_bound {κ c s : ℝ} (hc : 0 < c) (hκ : c ≤ κ) (hs : 0 ≤ s)
    (p : ℂ[X]) (D : ℕ) (hp : p.natDegree < D) :
    ‖polynomialProfile κ p s‖ ≤ profileBound c D (fun j => ‖p.coeff j‖) := by
  have he : Real.exp (-κ * s) ≤ Real.exp (-c * s) := Real.exp_le_exp.mpr (by nlinarith)
  rw [polynomialProfile, norm_smul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _),
    eval_eq_sum_range' hp]
  calc
    Real.exp (-κ * s) * ‖∑ j ∈ range D, p.coeff j * (s : ℂ) ^ j‖ ≤
        Real.exp (-κ * s) * ∑ j ∈ range D, ‖p.coeff j * (s : ℂ) ^ j‖ :=
      mul_le_mul_of_nonneg_left (norm_sum_le _ _) (Real.exp_nonneg _)
    _ = ∑ j ∈ range D, ‖p.coeff j‖ * (s ^ j * Real.exp (-κ * s)) := by
      rw [mul_sum]
      apply sum_congr rfl
      intro j hj
      simp only [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hs]
      ring
    _ ≤ profileBound c D (fun j => ‖p.coeff j‖) := by
      apply sum_le_sum
      intro j hj
      have hjb := (mul_le_mul_of_nonneg_left he (pow_nonneg hs j)).trans
        (pow_mul_exp_neg_mul_le hc hs j)
      simpa only [mul_div_assoc] using mul_le_mul_of_nonneg_left hjb (norm_nonneg (p.coeff j))

theorem polynomialProfile_split_exp (κ c : ℝ) (p : ℂ[X]) (s : ℝ) :
    polynomialProfile κ p s = Real.exp (-c * s) • polynomialProfile (κ - c) p s := by
  rw [polynomialProfile, polynomialProfile, smul_smul, ← Real.exp_add]
  congr 2
  ring

theorem norm_polynomialProfile_le_exp_bound {κ c s : ℝ} (hc : 0 < c) (hκ : c ≤ κ) (hs : 0 ≤ s)
    (p : ℂ[X]) (D : ℕ) (hp : p.natDegree < D) :
    ‖polynomialProfile κ p s‖ ≤
      profileBound (c / 2) D (fun j => ‖p.coeff j‖) * Real.exp (-(c / 2) * s) := by
  rw [polynomialProfile_split_exp κ (c / 2), norm_smul,
    Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  simpa only [mul_comm] using mul_le_mul_of_nonneg_left
    (norm_polynomialProfile_le_bound (by positivity : 0 < c / 2)
      (by linarith : c / 2 ≤ κ - c / 2) hs p D hp) (Real.exp_nonneg (-(c / 2) * s))

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem exists_positive_lower_bound_on_compact {K : Set E} (hK : IsCompact K)
    {κ : E → ℝ} (hκ : ContinuousOn κ K) (hpos : ∀ y ∈ K, 0 < κ y) :
    ∃ c : ℝ, 0 < c ∧ ∀ y ∈ K, c ≤ κ y := by
  by_cases hne : K.Nonempty
  · obtain ⟨y, hy, hmin⟩ := hK.exists_isMinOn hne hκ
    exact ⟨κ y, hpos y hy, fun z hz => hmin hz⟩
  · exact ⟨1, zero_lt_one, fun y hy => (hne ⟨y, hy⟩).elim⟩

theorem exists_uniform_polynomialProfile_exp_bound_of_lower_bound
    {U K : Set E} (hK : IsCompact K) (hKU : K ⊆ U)
    {κ : E → ℝ} {c : ℝ} (hc : 0 < c) (hcκ : ∀ y ∈ K, c ≤ κ y)
    {P : E → ℂ[X]} (hP : CoeffContDiffOn P U) (D : ℕ)
    (hD : ∀ y ∈ K, (P y).natDegree < D) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ y ∈ K, ∀ s : ℝ, 0 ≤ s →
      ‖polynomialProfile (κ y) (P y) s‖ ≤ C * Real.exp (-(c / 2) * s) := by
  have hcoeff : ∀ j : ℕ, ∃ b : ℝ, ∀ y ∈ K, ‖(P y).coeff j‖ ≤ b :=
    fun j => hK.exists_bound_of_continuousOn ((hP j).continuousOn.mono hKU)
  choose b hb using hcoeff
  let B : ℕ → ℝ := fun j => max 0 (b j)
  refine ⟨profileBound (c / 2) D B,
    profileBound_nonneg (by positivity) D (fun j => le_max_left _ _), ?_⟩
  intro y hy s hs
  apply (norm_polynomialProfile_le_exp_bound hc (hcκ y hy) hs (P y) D (hD y hy)).trans
  apply mul_le_mul_of_nonneg_right ?_ (Real.exp_nonneg _)
  apply sum_le_sum
  intro j hj
  exact div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_right ((hb j y hy).trans (le_max_right _ _)) (Nat.cast_nonneg _))
    (pow_nonneg (by positivity : 0 ≤ c / 2) j)

theorem exists_uniform_polynomialProfile_exp_bound
    {U K : Set E} (hK : IsCompact K) (hKU : K ⊆ U)
    {κ : E → ℝ} (hκ : ContDiffOn ℝ ∞ κ U) (hpos : ∀ y ∈ U, 0 < κ y)
    {P : E → ℂ[X]} (hP : CoeffContDiffOn P U) (D : ℕ)
    (hD : ∀ y ∈ K, (P y).natDegree < D) :
    ∃ c C : ℝ, 0 < c ∧ 0 ≤ C ∧ ∀ y ∈ K, ∀ s : ℝ, 0 ≤ s →
      ‖polynomialProfile (κ y) (P y) s‖ ≤ C * Real.exp (-c * s) := by
  obtain ⟨c, hc, hcκ⟩ := exists_positive_lower_bound_on_compact hK
    (hκ.continuousOn.mono hKU) (fun y hy => hpos y (hKU hy))
  obtain ⟨C, hC, hbound⟩ := exists_uniform_polynomialProfile_exp_bound_of_lower_bound
    hK hKU hc hcκ hP D hD
  exact ⟨c / 2, C, by positivity, hC, hbound⟩

end CalderonPatch.BoundaryLayer

open Polynomial Set Finset
open scoped ContDiff
namespace CalderonPatch.BoundaryLayer
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem exists_uniform_finite_profile_exp_bound
    {ι : Type*} [Fintype ι] {U K : Set E} (hK : IsCompact K) (hKU : K ⊆ U)
    {κ : E → ℝ} (hκ : ContDiffOn ℝ ∞ κ U) (hpos : ∀ y ∈ U, 0 < κ y)
    (P : ι → E → ℂ[X]) (hP : ∀ i, CoeffContDiffOn (P i) U) (D : ι → ℕ)
    (hD : ∀ i y, y ∈ K → (P i y).natDegree < D i) :
    ∃ c C : ℝ, 0 < c ∧ 0 ≤ C ∧ ∀ i y, y ∈ K → ∀ s : ℝ, 0 ≤ s →
      ‖polynomialProfile (κ y) (P i y) s‖ ≤ C * Real.exp (-c * s) := by
  obtain ⟨c, hc, hcκ⟩ := exists_positive_lower_bound_on_compact hK
    (hκ.continuousOn.mono hKU) (fun y hy => hpos y (hKU hy))
  have hi : ∀ i, ∃ C : ℝ, 0 ≤ C ∧ ∀ y ∈ K, ∀ s : ℝ, 0 ≤ s →
      ‖polynomialProfile (κ y) (P i y) s‖ ≤ C * Real.exp (-(c / 2) * s) :=
    fun i => exists_uniform_polynomialProfile_exp_bound_of_lower_bound hK hKU hc hcκ (hP i) (D i) (hD i)
  choose C hC hbound using hi
  refine ⟨c / 2, ∑ i, C i, by positivity, sum_nonneg (fun i _ => hC i), ?_⟩
  intro i y hy s hs
  apply (hbound i y hy s hs).trans
  exact mul_le_mul_of_nonneg_right (single_le_sum (fun j _ => hC j) (mem_univ i)) (Real.exp_nonneg _)

theorem exists_uniform_profile_moment_exp_bound
    {U K : Set E} (hK : IsCompact K) (hKU : K ⊆ U)
    {κ : E → ℝ} (hκ : ContDiffOn ℝ ∞ κ U) (hpos : ∀ y ∈ U, 0 < κ y)
    {P : E → ℂ[X]} (hP : CoeffContDiffOn P U) (D : ℕ)
    (hD : ∀ y ∈ K, (P y).natDegree < D) (m : ℕ) :
    ∃ c C : ℝ, 0 < c ∧ 0 ≤ C ∧ ∀ y ∈ K, ∀ s : ℝ, 0 ≤ s →
      s ^ m * ‖polynomialProfile (κ y) (P y) s‖ ≤ C * Real.exp (-c * s) := by
  let Q : E → ℂ[X] := fun y => X ^ m * P y
  have hQ : CoeffContDiffOn Q U := (CoeffContDiffOn.const (X ^ m) U).mul hP
  have hd : ∀ y ∈ K, (Q y).natDegree < m + D := by
    intro y hy
    exact (natDegree_mul_le.trans (Nat.add_le_add_right (natDegree_X_pow_le m) _)).trans_lt
      (Nat.add_lt_add_left (hD y hy) m)
  obtain ⟨c, C, hc, hC, hb⟩ := exists_uniform_polynomialProfile_exp_bound hK hKU hκ hpos hQ (m + D) hd
  refine ⟨c, C, hc, hC, ?_⟩
  intro y hy s hs
  have he : ‖polynomialProfile (κ y) (Q y) s‖ = s ^ m * ‖polynomialProfile (κ y) (P y) s‖ := by
    simp only [Q, polynomialProfile, norm_smul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _),
      eval_mul, eval_pow, eval_X, norm_mul, norm_pow, Complex.norm_real, abs_of_nonneg hs]
    ring
  rw [← he]
  exact hb y hy s hs

theorem exponential_profile_tail_bound
    {κ C c δ t h : ℝ} (hC : 0 ≤ C) (hc : 0 < c) (hδ : 0 < δ)
    (hh : 0 < h) (ht : δ ≤ t) (p : ℂ[X])
    (hp : ‖polynomialProfile κ p (t / h)‖ ≤ C * Real.exp (-c * (t / h))) (K d : ℕ) :
    ‖polynomialProfile κ p (t / h)‖ / h ^ d ≤
      (C * ((K + d).factorial : ℝ) / (c * δ) ^ (K + d)) * h ^ K := by
  have hde : δ / h ≤ t / h := div_le_div_of_nonneg_right ht hh.le
  have he : Real.exp (-c * (t / h)) ≤ Real.exp (-(c * δ) / h) := by
    apply Real.exp_le_exp.mpr
    calc
      -c * (t / h) ≤ -c * (δ / h) := mul_le_mul_of_nonpos_left hde (neg_nonpos.mpr hc.le)
      _ = -(c * δ) / h := by ring
  have hp' := hp.trans (mul_le_mul_of_nonneg_left he hC)
  have hb := exp_neg_div_div_pow_le (mul_pos hc hδ) hh K d
  calc
    ‖polynomialProfile κ p (t / h)‖ / h ^ d ≤ C * Real.exp (-(c * δ) / h) / h ^ d :=
      div_le_div_of_nonneg_right hp' (pow_nonneg hh.le d)
    _ = C * (Real.exp (-(c * δ) / h) / h ^ d) := by ring
    _ ≤ C * (((K + d).factorial : ℝ) / (c * δ) ^ (K + d) * h ^ K) :=
      mul_le_mul_of_nonneg_left hb hC
    _ = _ := by ring

end CalderonPatch.BoundaryLayer

open Polynomial Set Finset
open scoped ContDiff
namespace CalderonPatch.BoundaryLayer
variable {n : ℕ}
local notation "Y" => EuclideanSpace ℝ (Fin n)

@[expose] def tangentialPhaseRead (ξ : Fin n → ℝ) (h : ℝ) : Y →L[ℝ] ℝ :=
  h⁻¹ • ∑ i : Fin n, ξ i • PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin n => ℝ) i

@[expose] def tangentialWave (ξ : Fin n → ℝ) (h : ℝ) (y : Y) : ℂ :=
  Complex.exp (Complex.I * (tangentialPhaseRead ξ h y : ℂ))

theorem tangentialWave_contDiff (ξ : Fin n → ℝ) (h : ℝ) : ContDiff ℝ ∞ (tangentialWave ξ h) :=
  (contDiff_const.mul (Complex.ofRealCLM.contDiff.comp (tangentialPhaseRead ξ h).contDiff)).cexp

theorem norm_tangentialWave (ξ : Fin n → ℝ) (h : ℝ) (y : Y) : ‖tangentialWave ξ h y‖ = 1 := by
  simp [tangentialWave, Complex.norm_exp]

namespace BoundaryLayerCoefficients

@[expose] def finiteWave {ξ : Fin n → ℝ} {U : Set Y} (B : BoundaryLayerCoefficients ξ U)
    (a : Y → ℂ) (η : ℝ → ℝ) (N : ℕ) (h : ℝ) (x : Y × ℝ) : ℂ :=
  tangentialWave ξ h x.1 * ∑ j ∈ range (N + 1),
    (h ^ j : ℂ) * cutoffProfileFamily η B.kappa (B.layerPolynomial a j) h x

theorem finiteWave_contDiff {ξ : Fin n → ℝ} {U : Set Y} (B : BoundaryLayerCoefficients ξ U)
    (hU : IsOpen U) {K : Set Y} (hK : IsClosed K) (hKU : K ⊆ U) (a : Y → ℂ)
    (ha : ContDiffOn ℝ ∞ a U) (ha0 : ∀ y ∉ K, a y = 0)
    (η : ℝ → ℝ) (hη : ContDiff ℝ ∞ η) (N : ℕ) (h : ℝ) :
    ContDiff ℝ ∞ (B.finiteWave a η N h) := by
  apply ((tangentialWave_contDiff ξ h).comp contDiff_fst).mul
  apply ContDiff.sum
  intro j hj
  exact contDiff_const.mul (B.cutoffProfile_contDiff hU hK hKU a ha ha0 j η hη h)

theorem finiteWave_tsupport_subset {ξ : Fin n → ℝ} {U : Set Y} (B : BoundaryLayerCoefficients ξ U)
    (hU : IsOpen U) {K : Set Y} (hK : IsClosed K) (a : Y → ℂ)
    (ha : ContDiffOn ℝ ∞ a U) (ha0 : ∀ y ∉ K, a y = 0)
    (η : ℝ → ℝ) (N : ℕ) (h : ℝ) : tsupport (B.finiteWave a η N h) ⊆ K ×ˢ tsupport η := by
  apply closure_minimal ?_ (hK.prod (isClosed_tsupport η))
  intro x hx
  by_contra hout
  have hz (j : ℕ) : cutoffProfileFamily η B.kappa (B.layerPolynomial a j) h x = 0 := by
    apply image_eq_zero_of_notMem_tsupport
    intro hm
    exact hout ((cutoffProfileFamily_tsupport_subset η B.kappa _ h hK
      (B.layerPolynomial_properties hU hK a ha ha0 j).2.2) hm)
  exact hx (by simp only [finiteWave, hz, mul_zero, sum_const_zero])

theorem finiteWave_hasCompactSupport {ξ : Fin n → ℝ} {U : Set Y} (B : BoundaryLayerCoefficients ξ U)
    (hU : IsOpen U) {K : Set Y} (hK : IsCompact K) (a : Y → ℂ)
    (ha : ContDiffOn ℝ ∞ a U) (ha0 : ∀ y ∉ K, a y = 0)
    (η : ℝ → ℝ) (hη : HasCompactSupport η) (N : ℕ) (h : ℝ) :
    HasCompactSupport (B.finiteWave a η N h) :=
  (hK.prod hη).of_isClosed_subset (isClosed_tsupport _)
    (B.finiteWave_tsupport_subset hU hK.isClosed a ha ha0 η N h)

theorem profile_face_base {ξ : Fin n → ℝ} {U : Set Y} (B : BoundaryLayerCoefficients ξ U)
    (a : Y → ℂ) (y : Y) : B.profile a 0 (y, 0) = a y := by
  simp [profile, B.layerPolynomial_zero, polynomialProfile]

theorem finiteWave_face {ξ : Fin n → ℝ} {U : Set Y} (B : BoundaryLayerCoefficients ξ U)
    (a : Y → ℂ) (η : ℝ → ℝ) (hη : η 0 = 1) (N : ℕ) (h : ℝ) (y : Y) :
    B.finiteWave a η N h (y, 0) = tangentialWave ξ h y * a y := by
  unfold finiteWave
  congr 1
  rw [sum_eq_single 0]
  · simpa only [cutoffProfileFamily, polynomialProfileFamily, polynomialProfile, profile, zero_div, hη, one_smul, pow_zero,
      Complex.ofReal_one, one_mul] using B.profile_face_base a y
  · intro j hj hj0
    have he := B.profile_face_zero a j (Nat.pos_of_ne_zero hj0) y
    simpa only [cutoffProfileFamily, polynomialProfileFamily, polynomialProfile, profile, zero_div, polynomialProfileFamily, polynomialProfile, profile, smul_zero, mul_zero] using congrArg
      (fun z : ℂ => (h ^ j : ℂ) * (η 0 • z)) he
  · intro h0
    exact (h0 (mem_range.mpr (Nat.zero_lt_succ N))).elim

end BoundaryLayerCoefficients
end CalderonPatch.BoundaryLayer

open Polynomial Set Finset
open scoped ContDiff
namespace CalderonPatch.BoundaryLayer
variable {n : ℕ}
local notation "Y" => EuclideanSpace ℝ (Fin n)

theorem hasDerivAt_cutoffProfile_normal
    (η : ℝ → ℝ) (hη : HasDerivAt η 0 0) (hη0 : η 0 = 1)
    (κ : Y → ℝ) (P : Y → ℂ[X]) (h : ℝ) (y : Y) :
    HasDerivAt (fun t => cutoffProfileFamily η κ P h (y, t))
      ((profileDerivative (κ y) (P y)).eval 0 / (h : ℂ)) 0 := by
  have hp0 : HasDerivAt (polynomialProfile (κ y) (P y))
      (polynomialProfile (κ y) (profileDerivative (κ y) (P y)) 0) ((0 : ℝ) / h) := by
    simpa only [zero_div] using hasDerivAt_polynomialProfile (κ y) (P y) 0
  have hscale : HasDerivAt (fun t : ℝ => t / h) (1 / h) 0 := by
    simpa only [id_eq] using (hasDerivAt_id (0 : ℝ)).div_const h
  have hp := hp0.scomp 0 hscale
  have hp' : HasDerivAt (fun t : ℝ => polynomialProfile (κ y) (P y) (t / h))
      ((profileDerivative (κ y) (P y)).eval 0 / (h : ℂ)) 0 := by
    have he : (1 / h) • polynomialProfile (κ y) (profileDerivative (κ y) (P y)) 0 =
        ((profileDerivative (κ y) (P y)).eval 0 / (h : ℂ)) := by
      simp [polynomialProfile, Complex.real_smul, div_eq_mul_inv, mul_comm]
    rw [he] at hp
    exact hp
  change HasDerivAt (fun t : ℝ => η t • polynomialProfile (κ y) (P y) (t / h)) _ 0
  convert hη.smul hp' using 1 <;> simp only [hη0, one_smul, zero_smul, add_zero]

namespace BoundaryLayerCoefficients

@[expose] def traceCoefficient {ξ : Fin n → ℝ} {U : Set Y} (B : BoundaryLayerCoefficients ξ U)
    (a : Y → ℂ) (j : ℕ) (y : Y) : ℂ :=
  (profileDerivative (B.kappa y) (B.layerPolynomial a j y)).eval 0

theorem traceCoefficient_zero {ξ : Fin n → ℝ} {U : Set Y} (B : BoundaryLayerCoefficients ξ U)
    (a : Y → ℂ) (y : Y) : B.traceCoefficient a 0 y = -(B.kappa y : ℂ) * a y := by
  simp [traceCoefficient, B.layerPolynomial_zero, profileDerivative]

theorem traceCoefficient_positive {ξ : Fin n → ℝ} {U : Set Y} (B : BoundaryLayerCoefficients ξ U)
    (hU : IsOpen U) {K : Set Y} (hK : IsClosed K) (a : Y → ℂ)
    (ha : ContDiffOn ℝ ∞ a U) (ha0 : ∀ y ∉ K, a y = 0)
    (j : ℕ) (hj : 0 < j) {y : Y} (hy : y ∈ U) :
    B.traceCoefficient a j y = polynomialTrace (2 * (B.kappa y : ℂ)) (B.layerForcing a j y) := by
  unfold traceCoefficient profileDerivative
  rw [eval_sub, eval_mul, eval_C, B.layerPolynomial_face_zero a j hj y, mul_zero, sub_zero]
  exact triangularLayerPolynomial_trace (B.transportSystem hU K hK) B.transportScale a
    B.transportScale_smooth (fun z hz => B.transportScale_ne_zero hz) ha ha0 j hj hy

theorem hasDerivAt_finiteWave_normal {ξ : Fin n → ℝ} {U : Set Y} (B : BoundaryLayerCoefficients ξ U)
    (a : Y → ℂ) (η : ℝ → ℝ) (hη : HasDerivAt η 0 0) (hη0 : η 0 = 1)
    (N : ℕ) (h : ℝ) (y : Y) :
    HasDerivAt (fun t => B.finiteWave a η N h (y, t))
      (tangentialWave ξ h y * ((∑ j ∈ range (N + 1), (h ^ j : ℂ) * B.traceCoefficient a j y) / (h : ℂ))) 0 := by
  have hs : HasDerivAt
      (fun t : ℝ => ∑ j ∈ range (N + 1), (h ^ j : ℂ) *
        cutoffProfileFamily η B.kappa (B.layerPolynomial a j) h (y, t))
      (∑ j ∈ range (N + 1), (h ^ j : ℂ) * (B.traceCoefficient a j y / (h : ℂ))) 0 := by
    apply HasDerivAt.fun_sum
    intro j hj
    exact (hasDerivAt_cutoffProfile_normal η hη hη0 B.kappa (B.layerPolynomial a j) h y).const_mul _
  convert hs.const_mul (tangentialWave ξ h y) using 1
  · rfl
  · simp only [← mul_div_assoc, sum_div]

theorem finiteWave_scaled_trace {ξ : Fin n → ℝ} {U : Set Y} (B : BoundaryLayerCoefficients ξ U)
    (a : Y → ℂ) (η : ℝ → ℝ) (hη : HasDerivAt η 0 0) (hη0 : η 0 = 1)
    (N : ℕ) {h : ℝ} (hh : h ≠ 0) (y : Y) :
    (h : ℂ) * (tangentialWave ξ h y)⁻¹ * deriv (fun t => B.finiteWave a η N h (y, t)) 0 =
      ∑ j ∈ range (N + 1), (h ^ j : ℂ) * B.traceCoefficient a j y := by
  rw [(B.hasDerivAt_finiteWave_normal a η hη hη0 N h y).deriv]
  have hw : tangentialWave ξ h y ≠ 0 := Complex.exp_ne_zero _
  have hh' : (h : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hh
  field_simp

end BoundaryLayerCoefficients
end CalderonPatch.BoundaryLayer

open Set Filter Topology
open scoped ContDiff
namespace CalderonPatch.BoundaryLayer
variable {n : ℕ}
local notation "Y" => EuclideanSpace ℝ (Fin n)

@[expose] def phaseRate (ξ : Fin n → ℝ) (h : ℝ) (v : Y) : ℂ :=
  Complex.I * (tangentialPhaseRead ξ h v : ℂ)

theorem tangentialPhaseRead_basis (ξ : Fin n → ℝ) (h : ℝ) (i : Fin n) :
    tangentialPhaseRead ξ h (EuclideanSpace.basisFun (Fin n) ℝ i) = ξ i / h := by
  simp [tangentialPhaseRead, EuclideanSpace.basisFun_apply, PiLp.single_apply, div_eq_mul_inv, mul_comm]

theorem fderiv_tangentialWave_direction (ξ : Fin n → ℝ) (h : ℝ) (y v : Y) :
    fderiv ℝ (tangentialWave ξ h) y v = tangentialWave ξ h y * phaseRate ξ h v := by
  have hd := ((Complex.ofRealCLM.hasFDerivAt.comp y (tangentialPhaseRead ξ h).hasFDerivAt).const_mul Complex.I).cexp
  change fderiv ℝ (fun x => Complex.exp (Complex.I * (Complex.ofRealCLM ∘ tangentialPhaseRead ξ h) x)) y v = _
  rw [hd.fderiv]
  change Complex.exp (Complex.I * (tangentialPhaseRead ξ h y : ℂ)) *
    (Complex.I * (tangentialPhaseRead ξ h v : ℂ)) = _
  rfl

theorem fderiv_tangentialWave_mul_direction (ξ : Fin n → ℝ) (h : ℝ) {f : Y → ℂ}
    {y : Y} (hf : DifferentiableAt ℝ f y) (v : Y) :
    fderiv ℝ (fun x => tangentialWave ξ h x * f x) y v =
      tangentialWave ξ h y * (phaseRate ξ h v * f y + fderiv ℝ f y v) := by
  rw [fderiv_fun_mul ((tangentialWave_contDiff ξ h).differentiable (by decide) y) hf]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
  rw [fderiv_tangentialWave_direction]
  ring

theorem fderiv_twice_tangentialWave_mul_direction
    (ξ : Fin n → ℝ) (h : ℝ) {U : Set Y} (hU : IsOpen U) {f : Y → ℂ}
    (hf : ContDiffOn ℝ ∞ f U) {y : Y} (hy : y ∈ U) (u v : Y) :
    fderiv ℝ (fun x => fderiv ℝ (fun z => tangentialWave ξ h z * f z) x v) y u =
      tangentialWave ξ h y *
        (phaseRate ξ h u * phaseRate ξ h v * f y +
          phaseRate ξ h v * fderiv ℝ f y u + phaseRate ξ h u * fderiv ℝ f y v +
            fderiv ℝ (fun x => fderiv ℝ f x v) y u) := by
  have hdf : ContDiffOn ℝ ∞ (fun x => fderiv ℝ f x v) U :=
    (hf.fderiv_of_isOpen hU (by simp : (∞ : ℕ∞ω) + 1 ≤ ∞)).clm_apply contDiffOn_const
  have hfy : DifferentiableAt ℝ f y := (hf y hy).contDiffAt (hU.mem_nhds hy) |>.differentiableAt (by decide)
  have hdfy : DifferentiableAt ℝ (fun x => fderiv ℝ f x v) y :=
    (hdf y hy).contDiffAt (hU.mem_nhds hy) |>.differentiableAt (by decide)
  have he : (fun x => fderiv ℝ (fun z => tangentialWave ξ h z * f z) x v) =ᶠ[𝓝 y]
      (fun x => tangentialWave ξ h x * (phaseRate ξ h v * f x + fderiv ℝ f x v)) := by
    filter_upwards [hU.mem_nhds hy] with x hx
    exact fderiv_tangentialWave_mul_direction ξ h
      ((hf x hx).contDiffAt (hU.mem_nhds hx) |>.differentiableAt (by decide)) v
  have hinner : DifferentiableAt ℝ (fun x => phaseRate ξ h v * f x + fderiv ℝ f x v) y :=
    (hfy.const_mul (phaseRate ξ h v)).add hdfy
  rw [he.fderiv_eq, fderiv_tangentialWave_mul_direction ξ h hinner u]
  rw [fderiv_fun_add (hfy.const_mul _) hdfy, fderiv_const_mul hfy (phaseRate ξ h v)]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
  ring

end CalderonPatch.BoundaryLayer

open Polynomial Set Filter Topology Finset
open scoped ContDiff
namespace CalderonPatch.BoundaryLayer

theorem polynomialProfile_add (κ : ℝ) (p q : ℂ[X]) (s : ℝ) :
    polynomialProfile κ (p + q) s = polynomialProfile κ p s + polynomialProfile κ q s := by
  simp [polynomialProfile, smul_add]

theorem polynomialProfile_neg (κ : ℝ) (p : ℂ[X]) (s : ℝ) :
    polynomialProfile κ (-p) s = -polynomialProfile κ p s := by
  simp [polynomialProfile]

theorem polynomialProfile_sum {ι : Type*} (κ : ℝ) (A : Finset ι) (p : ι → ℂ[X]) (s : ℝ) :
    polynomialProfile κ (∑ i ∈ A, p i) s = ∑ i ∈ A, polynomialProfile κ (p i) s := by
  simp only [polynomialProfile, eval_finsetSum, smul_sum]

theorem polynomialProfile_C_X_mul (κ : ℝ) (c : ℂ) (l : ℕ) (p : ℂ[X]) (s : ℝ) :
    polynomialProfile κ (C c * X ^ l * p) s = c * (s : ℂ) ^ l * polynomialProfile κ p s := by
  simp only [polynomialProfile, eval_mul, eval_C, eval_pow, eval_X, Complex.real_smul]
  ring

theorem polynomialProfile_C_mul (κ : ℝ) (c : ℂ) (p : ℂ[X]) (s : ℝ) :
    polynomialProfile κ (C c * p) s = c * polynomialProfile κ p s := by
  simpa only [pow_zero, mul_one] using polynomialProfile_C_X_mul κ c 0 p s

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem CoeffContDiffOn.profile_slice {U : Set E} {P : E → ℂ[X]} {κ : E → ℝ}
    (hP : CoeffContDiffOn P U) (hκ : ContDiffOn ℝ ∞ κ U) (D : ℕ)
    (hD : ∀ y ∈ U, (P y).natDegree ≤ D) (s : ℝ) :
    ContDiffOn ℝ ∞ (fun y => polynomialProfile (κ y) (P y) s) U :=
  ((hκ.neg.mul contDiffOn_const).exp).smul (hP.eval_const D hD s)

theorem fderiv_twice_polynomialProfile_direction {U : Set E} (hU : IsOpen U)
    {P : E → ℂ[X]} {κ : E → ℝ} (hP : CoeffContDiffOn P U) (hκ : ContDiffOn ℝ ∞ κ U)
    (D : ℕ) (hD : ∀ x ∈ U, (P x).natDegree ≤ D) {y : E} (hy : y ∈ U) (s : ℝ) (u v : E) :
    fderiv ℝ (fun x => fderiv ℝ (fun z => polynomialProfile (κ z) (P z) s) x v) y u =
      polynomialProfile (κ y) (profileSpatialDeriv (D + 1) u κ (profileSpatialDeriv D v κ P) y) s := by
  have he : (fun x => fderiv ℝ (fun z => polynomialProfile (κ z) (P z) s) x v) =ᶠ[𝓝 y]
      (fun x => polynomialProfile (κ x) (profileSpatialDeriv D v κ P x) s) := by
    filter_upwards [hU.mem_nhds hy] with x hx
    exact fderiv_polynomialProfile_direction hU hP hκ D hD hx s v
  rw [he.fderiv_eq]
  exact fderiv_polynomialProfile_direction hU (hP.profileSpatialDeriv hU hκ D v) hκ (D + 1)
    (fun x hx => profileSpatialDeriv_natDegree_le D v κ P (hD x hx)) hy s u

end CalderonPatch.BoundaryLayer

open Polynomial Set Finset
open scoped ContDiff
namespace CalderonPatch.BoundaryLayer.BoundaryLayerCoefficients
variable {n : ℕ}
local notation "Y" => EuclideanSpace ℝ (Fin n)
local notation "e" => EuclideanSpace.basisFun (Fin n) ℝ

theorem principalTerm_read {ξ : Fin n → ℝ} {U : Set Y} (B : BoundaryLayerCoefficients ξ U)
    (l : ℕ) (P : Y → ℂ[X]) (y : Y) (s : ℝ) :
    polynomialProfile (B.kappa y) (B.principalTerm l P y) s =
      (∑ i, ∑ j, B.inverse l i j y * (ξ i : ℂ) * (ξ j : ℂ)) *
        (s : ℂ) ^ l * polynomialProfile (B.kappa y) (P y) s :=
  polynomialProfile_C_X_mul _ _ _ _ _

theorem normalTerm_read {ξ : Fin n → ℝ} {U : Set Y} (B : BoundaryLayerCoefficients ξ U)
    (l : ℕ) (P : Y → ℂ[X]) (y : Y) (s : ℝ) :
    polynomialProfile (B.kappa y) (B.normalTerm l P y) s =
      (B.normalDrift (l - 1) y / 2) * (s : ℂ) ^ (l - 1) *
        deriv (polynomialProfile (B.kappa y) (P y)) s := by
  rw [deriv_polynomialProfile]
  exact polynomialProfile_C_X_mul _ _ _ _ _

theorem crossTerm_read {ξ : Fin n → ℝ} {U : Set Y} (B : BoundaryLayerCoefficients ξ U)
    (hU : IsOpen U) (l d : ℕ) {P : Y → ℂ[X]} (hP : CoeffContDiffOn P U)
    (hD : ∀ y ∈ U, (P y).natDegree ≤ d) {y : Y} (hy : y ∈ U) (s : ℝ) :
    polynomialProfile (B.kappa y) (B.crossTerm l d P y) s =
      (-2 * Complex.I) * ∑ i, ∑ j,
        (B.inverse (l - 1) i j y * (ξ i : ℂ)) * (s : ℂ) ^ (l - 1) *
          fderiv ℝ (fun x => polynomialProfile (B.kappa x) (P x) s) y (e j) := by
  unfold crossTerm
  rw [polynomialProfile_C_mul, polynomialProfile_sum]
  congr 1
  apply sum_congr rfl
  intro i hi
  rw [polynomialProfile_sum]
  apply sum_congr rfl
  intro j hj
  rw [polynomialProfile_C_X_mul, fderiv_polynomialProfile_direction hU hP B.kappa_smooth d hD hy s (e j)]

theorem phaseDriftTerm_read {ξ : Fin n → ℝ} {U : Set Y} (B : BoundaryLayerCoefficients ξ U)
    (l : ℕ) (P : Y → ℂ[X]) (y : Y) (s : ℝ) :
    polynomialProfile (B.kappa y) (B.phaseDriftTerm l P y) s =
      (-Complex.I) * ∑ i, (B.tangentDrift (l - 1) i y * (ξ i : ℂ)) *
        (s : ℂ) ^ (l - 1) * polynomialProfile (B.kappa y) (P y) s := by
  unfold phaseDriftTerm
  rw [polynomialProfile_C_mul, polynomialProfile_sum]
  congr 1
  apply sum_congr rfl
  intro i hi
  exact polynomialProfile_C_X_mul _ _ _ _ _

theorem tangentSecondTerm_read {ξ : Fin n → ℝ} {U : Set Y} (B : BoundaryLayerCoefficients ξ U)
    (hU : IsOpen U) (l d : ℕ) {P : Y → ℂ[X]} (hP : CoeffContDiffOn P U)
    (hD : ∀ y ∈ U, (P y).natDegree ≤ d) {y : Y} (hy : y ∈ U) (s : ℝ) :
    polynomialProfile (B.kappa y) (B.tangentSecondTerm l d P y) s =
      -(∑ i, ∑ j, B.inverse (l - 2) i j y * (s : ℂ) ^ (l - 2) *
        fderiv ℝ (fun x => fderiv ℝ (fun z => polynomialProfile (B.kappa z) (P z) s) x (e j)) y (e i)) := by
  unfold tangentSecondTerm
  rw [polynomialProfile_neg, polynomialProfile_sum]
  congr 1
  apply sum_congr rfl
  intro i hi
  rw [polynomialProfile_sum]
  apply sum_congr rfl
  intro j hj
  rw [polynomialProfile_C_X_mul,
    fderiv_twice_polynomialProfile_direction hU hP B.kappa_smooth d hD hy s (e i) (e j)]

theorem tangentFirstTerm_read {ξ : Fin n → ℝ} {U : Set Y} (B : BoundaryLayerCoefficients ξ U)
    (hU : IsOpen U) (l d : ℕ) {P : Y → ℂ[X]} (hP : CoeffContDiffOn P U)
    (hD : ∀ y ∈ U, (P y).natDegree ≤ d) {y : Y} (hy : y ∈ U) (s : ℝ) :
    polynomialProfile (B.kappa y) (B.tangentFirstTerm l d P y) s =
      -(∑ i, B.tangentDrift (l - 2) i y * (s : ℂ) ^ (l - 2) *
        fderiv ℝ (fun x => polynomialProfile (B.kappa x) (P x) s) y (e i)) := by
  unfold tangentFirstTerm
  rw [polynomialProfile_neg, polynomialProfile_sum]
  congr 1
  apply sum_congr rfl
  intro i hi
  rw [polynomialProfile_C_X_mul, fderiv_polynomialProfile_direction hU hP B.kappa_smooth d hD hy s (e i)]

end CalderonPatch.BoundaryLayer.BoundaryLayerCoefficients
