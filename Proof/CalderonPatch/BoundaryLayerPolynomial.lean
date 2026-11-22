/-
Adapted from the conformal Poisson Lean formalization by Cătălin I. Cârstea,
Tony Liimatainen, Yi-Hsuan Lin, and William Trad, BSD 3-Clause.
Source: arxiv-2610.13592-lean commit 4cfcab036aedbb4f825a3aeb366da12fe5673ddd.
See the source and license in references/conformal-poisson-4cfcab03.
-/
module

public import Mathlib.Algebra.Polynomial.Derivative
public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.InnerProductSpace.PiL2

import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Tactic

public section

noncomputable section

open Set Filter Topology
namespace CalderonPatch.BoundaryLayer

def finitePolynomial (N : ℕ) (c : ℕ → ℂ) (s : ℝ) : ℂ :=
  ∑ j ∈ Finset.range N, s ^ j • c j

def finitePrimitive (N : ℕ) (c : ℕ → ℂ) (s : ℝ) : ℂ :=
  ∑ j ∈ Finset.range N, (s ^ (j + 1) / (j + 1 : ℝ)) • c j

theorem finitePrimitive_zero (N : ℕ) (c : ℕ → ℂ) : finitePrimitive N c 0 = 0 := by
  simp [finitePrimitive]

theorem hasDerivAt_finitePrimitive (N : ℕ) (c : ℕ → ℂ) (s : ℝ) :
    HasDerivAt (finitePrimitive N c) (finitePolynomial N c s) s := by
  unfold finitePrimitive finitePolynomial
  apply HasDerivAt.fun_sum
  intro j hj
  have hn : (j + 1 : ℝ) ≠ 0 := by positivity
  have hd := ((hasDerivAt_pow (j + 1) s).div_const (j + 1 : ℝ)).smul_const (c j)
  convert hd using 1
  simp only [Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one]
  rw [mul_div_cancel_left₀ _ hn]

def integratedProfile (κ : ℝ) (c0 : ℂ) (N : ℕ) (c : ℕ → ℂ) (s : ℝ) : ℂ :=
  Real.exp (-κ * s) • (c0 + finitePrimitive N c s)

theorem integratedProfile_zero (κ : ℝ) (c0 : ℂ) (N : ℕ) (c : ℕ → ℂ) :
    integratedProfile κ c0 N c 0 = c0 := by
  simp [integratedProfile, finitePrimitive_zero]

theorem hasDerivAt_integratedProfile (κ : ℝ) (c0 : ℂ) (N : ℕ) (c : ℕ → ℂ) (s : ℝ) :
    HasDerivAt (integratedProfile κ c0 N c)
      (Real.exp (-κ * s) • finitePolynomial N c s - κ • integratedProfile κ c0 N c s) s := by
  have he : HasDerivAt (fun t : ℝ => Real.exp (-κ * t))
      ((-κ * Real.exp (-κ * s)) : ℝ) s := by
    convert ((hasDerivAt_id s).const_mul (-κ)).exp using 1 <;> simp [mul_comm]
  have hp := (hasDerivAt_finitePrimitive N c s).const_add c0
  convert he.smul hp using 1
  · funext t
    simp only [integratedProfile, Pi.smul_apply', neg_mul]
  · simp only [integratedProfile, sub_eq_add_neg, smul_smul, ← neg_smul, neg_mul]

theorem deriv_integratedProfile_zero (κ : ℝ) (c0 : ℂ) (N : ℕ) (c : ℕ → ℂ) :
    deriv (integratedProfile κ c0 N c) 0 = finitePolynomial N c 0 - κ • c0 := by
  simpa only [mul_zero, Real.exp_zero, one_smul, integratedProfile_zero] using
    (hasDerivAt_integratedProfile κ c0 N c 0).deriv

theorem pow_mul_exp_neg_mul_le {a s : ℝ} (ha : 0 < a) (hs : 0 ≤ s) (m : ℕ) :
    s ^ m * Real.exp (-a * s) ≤ (m.factorial : ℝ) / a ^ m := by
  have hfac : 0 < (m.factorial : ℝ) := Nat.cast_pos.mpr (Nat.factorial_pos m)
  have h0 := Real.pow_div_factorial_le_exp (a * s) (mul_nonneg ha.le hs) m
  have h1 := (div_le_iff₀ hfac).mp h0
  have h2 := mul_le_mul_of_nonneg_right h1 (Real.exp_nonneg (-a * s))
  have hcancel : Real.exp (a * s) * (m.factorial : ℝ) * Real.exp (-a * s) = m.factorial := by
    rw [mul_right_comm, ← Real.exp_add]
    simp
  rw [hcancel, mul_pow] at h2
  apply (le_div_iff₀ (pow_pos ha m)).mpr
  nlinarith [h2]

theorem exp_neg_div_le_mul_pow {a h : ℝ} (ha : 0 < a) (hh : 0 < h) (m : ℕ) :
    Real.exp (-a / h) ≤ (m.factorial : ℝ) / a ^ m * h ^ m := by
  have h0 := pow_mul_exp_neg_mul_le ha (inv_nonneg.mpr hh.le) m
  have h1 : (h ^ m)⁻¹ * Real.exp (-a / h) ≤ (m.factorial : ℝ) / a ^ m := by
    simpa only [inv_pow, div_eq_mul_inv] using h0
  have hp : 0 < h ^ m := pow_pos hh m
  have h2 := mul_le_mul_of_nonneg_left h1 hp.le
  rw [← mul_assoc, mul_inv_cancel₀ hp.ne', one_mul] at h2
  simpa only [mul_comm] using h2

theorem exp_neg_div_div_pow_le {a h : ℝ} (ha : 0 < a) (hh : 0 < h) (K d : ℕ) :
    Real.exp (-a / h) / h ^ d ≤ ((K + d).factorial : ℝ) / a ^ (K + d) * h ^ K := by
  apply (div_le_iff₀ (pow_pos hh d)).mpr
  simpa only [pow_add, mul_assoc] using exp_neg_div_le_mul_pow ha hh (K + d)

end CalderonPatch.BoundaryLayer

open Polynomial Finset
namespace CalderonPatch.BoundaryLayer

def polynomialResolvent (μ : ℂ) (N : ℕ) (p : ℂ[X]) : ℂ[X] :=
  ∑ k ∈ range N, C (μ⁻¹ ^ (k + 1)) * derivative^[k] p

theorem polynomialResolvent_equation (μ : ℂ) (hμ : μ ≠ 0) (N : ℕ) (p : ℂ[X]) :
    C μ * polynomialResolvent μ N p - derivative (polynomialResolvent μ N p) =
      p - C (μ⁻¹ ^ N) * derivative^[N] p := by
  induction N with
  | zero => simp [polynomialResolvent]
  | succ N ih =>
    have hmul : C μ * C (μ⁻¹ ^ (N + 1)) = (C (μ⁻¹ ^ N) : ℂ[X]) := by
      rw [← C_mul, pow_succ]
      congr 1
      calc
        μ * (μ⁻¹ ^ N * μ⁻¹) = μ⁻¹ ^ N * (μ * μ⁻¹) := by ring
        _ = μ⁻¹ ^ N := by rw [mul_inv_cancel₀ hμ, mul_one]
    have hs : polynomialResolvent μ (N + 1) p = polynomialResolvent μ N p +
        C (μ⁻¹ ^ (N + 1)) * derivative^[N] p := by
      simp only [polynomialResolvent, sum_range_succ]
    rw [hs, derivative_add, derivative_C_mul,
      ← Function.iterate_succ_apply' derivative N p]
    calc
      _ = (C μ * polynomialResolvent μ N p - derivative (polynomialResolvent μ N p)) +
          C μ * C (μ⁻¹ ^ (N + 1)) * derivative^[N] p -
          C (μ⁻¹ ^ (N + 1)) * derivative^[N + 1] p := by ring
      _ = p - C (μ⁻¹ ^ (N + 1)) * derivative^[N + 1] p := by rw [ih, hmul]; ring

theorem polynomialResolvent_solves (μ : ℂ) (hμ : μ ≠ 0) (p : ℂ[X]) :
    C μ * polynomialResolvent μ (p.natDegree + 1) p -
      derivative (polynomialResolvent μ (p.natDegree + 1) p) = p := by
  rw [polynomialResolvent_equation μ hμ,
    iterate_derivative_eq_zero (Nat.lt_succ_self _), mul_zero, sub_zero]

theorem polynomialResolvent_unique (μ : ℂ) (hμ : μ ≠ 0) (p q₁ q₂ : ℂ[X])
    (h₁ : C μ * q₁ - derivative q₁ = p)
    (h₂ : C μ * q₂ - derivative q₂ = p) : q₁ = q₂ := by
  have he : derivative (q₁ - q₂) = C μ * (q₁ - q₂) := by
    rw [derivative_sub]
    linear_combination -h₁ + h₂
  by_contra hne
  have hz : q₁ - q₂ ≠ 0 := sub_ne_zero.mpr hne
  have hlt := degree_derivative_lt hz
  rw [he, degree_C_mul_of_isUnit (isUnit_iff_ne_zero.mpr hμ)] at hlt
  exact lt_irrefl _ hlt

def polynomialPrimitive (p : ℂ[X]) : ℂ[X] :=
  p.sum fun j a => monomial (j + 1) (a / (j + 1 : ℂ))

theorem polynomialPrimitive_derivative (p : ℂ[X]) :
    derivative (polynomialPrimitive p) = p := by
  classical
  unfold polynomialPrimitive
  rw [Polynomial.sum, derivative_sum]
  simp_rw [derivative_monomial, Nat.add_sub_cancel_right]
  have h (j : ℕ) : (j + 1 : ℂ) ≠ 0 := by exact_mod_cast (Nat.succ_ne_zero j)
  simp_rw [Nat.cast_add, Nat.cast_one, div_mul_cancel₀ _ (h _)]
  exact p.sum_monomial_eq

theorem polynomialPrimitive_zero (p : ℂ[X]) : (polynomialPrimitive p).eval 0 = 0 := by
  classical
  simp [polynomialPrimitive, Polynomial.sum, eval_finsetSum]

def polynomialTransport (κ : ℝ) (p : ℂ[X]) : ℂ[X] :=
  polynomialPrimitive (polynomialResolvent (2 * (κ : ℂ)) (p.natDegree + 1) p)

theorem polynomialTransport_equation (κ : ℝ) (hκ : κ ≠ 0) (p : ℂ[X]) :
    C (2 * (κ : ℂ)) * derivative (polynomialTransport κ p) -
      derivative (derivative (polynomialTransport κ p)) = p := by
  rw [polynomialTransport, polynomialPrimitive_derivative]
  exact polynomialResolvent_solves _ (mul_ne_zero (by norm_num) (by exact_mod_cast hκ)) p

theorem polynomialTransport_zero (κ : ℝ) (p : ℂ[X]) :
    (polynomialTransport κ p).eval 0 = 0 := polynomialPrimitive_zero _

end CalderonPatch.BoundaryLayer

open Polynomial Finset
namespace CalderonPatch.BoundaryLayer

theorem polynomialResolvent_solves_of_degree_lt (μ : ℂ) (hμ : μ ≠ 0)
    (p : ℂ[X]) (D : ℕ) (hD : p.natDegree < D) :
    C μ * polynomialResolvent μ D p - derivative (polynomialResolvent μ D p) = p := by
  rw [polynomialResolvent_equation μ hμ, iterate_derivative_eq_zero hD, mul_zero, sub_zero]

def polynomialTrace (μ : ℂ) (p : ℂ[X]) : ℂ :=
  (polynomialResolvent μ (p.natDegree + 1) p).eval 0

theorem polynomialTrace_eq_of_degree_lt (μ : ℂ) (hμ : μ ≠ 0)
    (p : ℂ[X]) (D : ℕ) (hD : p.natDegree < D) :
    polynomialTrace μ p = (polynomialResolvent μ D p).eval 0 := by
  apply congrArg (Polynomial.eval 0)
  exact polynomialResolvent_unique μ hμ p _ _ (polynomialResolvent_solves μ hμ p)
    (polynomialResolvent_solves_of_degree_lt μ hμ p D hD)

theorem iterate_derivative_monomial_eval_zero (m k : ℕ) (a : ℂ) :
    (derivative^[k] (monomial m a)).eval 0 =
      if m = k then (m.factorial : ℂ) * a else 0 := by
  rw [← coeff_zero_eq_eval_zero, coeff_iterate_derivative]
  simp only [Nat.zero_add, coeff_monomial]
  split_ifs with h
  · subst k
    simp [Nat.descFactorial_self, nsmul_eq_mul]
  · simp [Finsupp.single_apply, h]

theorem polynomialTrace_monomial (μ : ℂ) (hμ : μ ≠ 0) (m : ℕ) (a : ℂ) :
    polynomialTrace μ (monomial m a) = μ⁻¹ ^ (m + 1) * (m.factorial : ℂ) * a := by
  classical
  rw [polynomialTrace_eq_of_degree_lt μ hμ _ (m + 1)
    (lt_of_le_of_lt (natDegree_monomial_le _) (Nat.lt_succ_self m))]
  simp only [polynomialResolvent, eval_finsetSum, eval_mul, eval_C,
    iterate_derivative_monomial_eval_zero]
  rw [sum_eq_single m]
  · simp [mul_assoc]
  · intro b hb hbm
    simp only [if_neg (Ne.symm hbm), mul_zero]
  · simp

theorem polynomialTrace_dividedMonomial (μ : ℂ) (hμ : μ ≠ 0) (m : ℕ) (a : ℂ) :
    polynomialTrace μ (monomial m (a / (m.factorial : ℂ))) = μ⁻¹ ^ (m + 1) * a := by
  rw [polynomialTrace_monomial μ hμ]
  have hm : (m.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero m
  field_simp

theorem polynomialTrace_sub (μ : ℂ) (hμ : μ ≠ 0) (p q : ℂ[X]) :
    polynomialTrace μ (p - q) = polynomialTrace μ p - polynomialTrace μ q := by
  have he : polynomialResolvent μ ((p - q).natDegree + 1) (p - q) =
      polynomialResolvent μ (p.natDegree + 1) p - polynomialResolvent μ (q.natDegree + 1) q := by
    apply polynomialResolvent_unique μ hμ (p - q) _ _
      (polynomialResolvent_solves μ hμ _)
    rw [derivative_sub]
    linear_combination polynomialResolvent_solves μ hμ p - polynomialResolvent_solves μ hμ q
  unfold polynomialTrace
  rw [he, eval_sub]

end CalderonPatch.BoundaryLayer

open Polynomial Finset
namespace CalderonPatch.BoundaryLayer

theorem polynomialPrimitive_eq_sum_of_degree_lt (p : ℂ[X]) (D : ℕ) (hD : p.natDegree < D) :
    polynomialPrimitive p = ∑ j ∈ range D, monomial (j + 1) (p.coeff j / (j + 1 : ℂ)) := by
  exact p.sum_over_range' (fun _ => by simp) D hD

theorem polynomialPrimitive_natDegree_le (p : ℂ[X]) (D : ℕ) (hD : p.natDegree < D) :
    (polynomialPrimitive p).natDegree ≤ D := by
  classical
  rw [polynomialPrimitive_eq_sum_of_degree_lt p D hD]
  apply natDegree_sum_le_of_forall_le
  intro i hi
  exact (natDegree_monomial_le _).trans (by have := mem_range.mp hi; omega)

theorem polynomialResolvent_natDegree_le (μ : ℂ) (D : ℕ) (p : ℂ[X]) :
    (polynomialResolvent μ D p).natDegree ≤ p.natDegree := by
  classical
  apply natDegree_sum_le_of_forall_le
  intro i hi
  exact (natDegree_C_mul_le _ _).trans ((natDegree_iterate_derivative p i).trans (Nat.sub_le _ _))

@[expose] def fixedDegreeTransport (μ : ℂ) (D : ℕ) (p : ℂ[X]) : ℂ[X] :=
  polynomialPrimitive (polynomialResolvent μ D p)

theorem fixedDegreeTransport_equation (μ : ℂ) (hμ : μ ≠ 0) (D : ℕ) (p : ℂ[X])
    (hD : p.natDegree < D) :
    C μ * derivative (fixedDegreeTransport μ D p) -
      derivative (derivative (fixedDegreeTransport μ D p)) = p := by
  rw [fixedDegreeTransport, polynomialPrimitive_derivative]
  exact polynomialResolvent_solves_of_degree_lt μ hμ p D hD

theorem fixedDegreeTransport_natDegree_le (μ : ℂ) (D : ℕ) (p : ℂ[X])
    (hD : p.natDegree < D) : (fixedDegreeTransport μ D p).natDegree ≤ D :=
  polynomialPrimitive_natDegree_le _ D ((polynomialResolvent_natDegree_le μ D p).trans_lt hD)

theorem fixedDegreeTransport_independent (μ : ℂ) (hμ : μ ≠ 0) (D₁ D₂ : ℕ) (p : ℂ[X])
    (h₁ : p.natDegree < D₁) (h₂ : p.natDegree < D₂) :
    fixedDegreeTransport μ D₁ p = fixedDegreeTransport μ D₂ p := by
  apply congrArg polynomialPrimitive
  exact polynomialResolvent_unique μ hμ p _ _
    (polynomialResolvent_solves_of_degree_lt μ hμ p D₁ h₁)
    (polynomialResolvent_solves_of_degree_lt μ hμ p D₂ h₂)

theorem fixedDegreeTransport_zero (μ : ℂ) (D : ℕ) : fixedDegreeTransport μ D 0 = 0 := by
  simp [fixedDegreeTransport, polynomialResolvent, polynomialPrimitive]

end CalderonPatch.BoundaryLayer

open Polynomial Finset Set
open scoped ContDiff
namespace CalderonPatch.BoundaryLayer
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

@[expose] def CoeffContDiffOn (P : E → ℂ[X]) (U : Set E) : Prop :=
  ∀ j : ℕ, ContDiffOn ℝ ∞ (fun y => (P y).coeff j) U

theorem polynomialPrimitive_coeff_zero (p : ℂ[X]) : (polynomialPrimitive p).coeff 0 = 0 := by
  rw [coeff_zero_eq_eval_zero, polynomialPrimitive_zero]

theorem polynomialPrimitive_coeff_succ (p : ℂ[X]) (j : ℕ) :
    (polynomialPrimitive p).coeff (j + 1) = p.coeff j / (j + 1 : ℂ) := by
  have he := congrArg (fun q : ℂ[X] => q.coeff j) (polynomialPrimitive_derivative p)
  rw [coeff_derivative] at he
  exact (eq_div_iff (by exact_mod_cast Nat.succ_ne_zero j : (j + 1 : ℂ) ≠ 0)).mpr (by
    simpa only [Nat.cast_add, Nat.cast_one] using he)

theorem CoeffContDiffOn.monomial {U : Set E} {f : E → ℂ}
    (hf : ContDiffOn ℝ ∞ f U) (j : ℕ) : CoeffContDiffOn (fun y => monomial j (f y)) U := by
  intro k
  by_cases h : j = k
  · subst k
    simpa only [coeff_monomial, Finsupp.single_eq_same, if_true] using hf
  · simpa only [coeff_monomial, Finsupp.single_apply, ite_eq_right h] using
      (contDiffOn_const : ContDiffOn ℝ ∞ (fun _ : E => (0 : ℂ)) U)

theorem CoeffContDiffOn.sum {U : Set E} {ι : Type*} (s : Finset ι) {P : ι → E → ℂ[X]}
    (hP : ∀ i ∈ s, CoeffContDiffOn (P i) U) : CoeffContDiffOn (fun y => ∑ i ∈ s, P i y) U := by
  intro j
  simp only [finsetSum_coeff]
  exact ContDiffOn.sum (fun i hi => hP i hi j)

theorem CoeffContDiffOn.add {U : Set E} {P Q : E → ℂ[X]}
    (hP : CoeffContDiffOn P U) (hQ : CoeffContDiffOn Q U) : CoeffContDiffOn (fun y => P y + Q y) U := by
  intro j
  simpa only [coeff_add] using (hP j).add (hQ j)

theorem CoeffContDiffOn.sub {U : Set E} {P Q : E → ℂ[X]}
    (hP : CoeffContDiffOn P U) (hQ : CoeffContDiffOn Q U) : CoeffContDiffOn (fun y => P y - Q y) U := by
  intro j
  simpa only [coeff_sub] using (hP j).sub (hQ j)

theorem CoeffContDiffOn.C_mul {U : Set E} {P : E → ℂ[X]} {f : E → ℂ}
    (hP : CoeffContDiffOn P U) (hf : ContDiffOn ℝ ∞ f U) :
    CoeffContDiffOn (fun y => C (f y) * P y) U := by
  intro j
  simpa only [coeff_C_mul] using hf.mul (hP j)

theorem CoeffContDiffOn.derivative {U : Set E} {P : E → ℂ[X]}
    (hP : CoeffContDiffOn P U) : CoeffContDiffOn (fun y => Polynomial.derivative (P y)) U := by
  intro j
  simpa only [coeff_derivative] using (hP (j + 1)).mul contDiffOn_const

theorem CoeffContDiffOn.iterate_derivative {U : Set E} {P : E → ℂ[X]}
    (hP : CoeffContDiffOn P U) (k : ℕ) : CoeffContDiffOn (fun y => Polynomial.derivative^[k] (P y)) U := by
  induction k with
  | zero => exact hP
  | succ k ih => simpa only [Function.iterate_succ_apply'] using ih.derivative

theorem CoeffContDiffOn.primitive {U : Set E} {P : E → ℂ[X]}
    (hP : CoeffContDiffOn P U) : CoeffContDiffOn (fun y => polynomialPrimitive (P y)) U := by
  intro j
  cases j with
  | zero => simpa only [polynomialPrimitive_coeff_zero] using
      (contDiffOn_const : ContDiffOn ℝ ∞ (fun _ : E => (0 : ℂ)) U)
  | succ j => simpa only [polynomialPrimitive_coeff_succ] using (hP j).div_const (j + 1 : ℂ)

theorem CoeffContDiffOn.resolvent {U : Set E} {P : E → ℂ[X]} {μ : E → ℂ}
    (hP : CoeffContDiffOn P U) (hμ : ContDiffOn ℝ ∞ μ U) (hμ0 : ∀ y ∈ U, μ y ≠ 0) (D : ℕ) :
    CoeffContDiffOn (fun y => polynomialResolvent (μ y) D (P y)) U := by
  apply CoeffContDiffOn.sum
  intro k hk
  exact (hP.iterate_derivative k).C_mul ((hμ.inv hμ0).pow (k + 1))

theorem CoeffContDiffOn.fixedDegreeTransport {U : Set E} {P : E → ℂ[X]} {μ : E → ℂ}
    (hP : CoeffContDiffOn P U) (hμ : ContDiffOn ℝ ∞ μ U) (hμ0 : ∀ y ∈ U, μ y ≠ 0) (D : ℕ) :
    CoeffContDiffOn (fun y => fixedDegreeTransport (μ y) D (P y)) U :=
  (hP.resolvent hμ hμ0 D).primitive

end CalderonPatch.BoundaryLayer

open Polynomial Finset Set
open scoped ContDiff
namespace CalderonPatch.BoundaryLayer
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem CoeffContDiffOn.eval {U : Set E} {P : E → ℂ[X]}
    (hP : CoeffContDiffOn P U) (D : ℕ) (hD : ∀ y ∈ U, (P y).natDegree < D) :
    ContDiffOn ℝ ∞ (fun x : E × ℝ => (P x.1).eval (x.2 : ℂ)) (U ×ˢ univ) := by
  have hs : ContDiffOn ℝ ∞
      (fun x : E × ℝ => ∑ j ∈ range D, (P x.1).coeff j * (x.2 : ℂ) ^ j) (U ×ˢ univ) := by
    apply ContDiffOn.sum
    intro j hj
    exact ((hP j).comp contDiffOn_fst (fun x (hx : x ∈ U ×ˢ (univ : Set ℝ)) => hx.1)).mul
      ((Complex.ofRealCLM.contDiff.comp_contDiffOn contDiffOn_snd).pow j)
  apply hs.congr
  intro x hx
  exact (P x.1).eval_eq_sum_range' (hD x.1 hx.1) (x.2 : ℂ)

@[expose] def polynomialProfileFamily (κ : E → ℝ) (P : E → ℂ[X]) (x : E × ℝ) : ℂ :=
  Real.exp (-κ x.1 * x.2) • (P x.1).eval (x.2 : ℂ)

theorem CoeffContDiffOn.profile {U : Set E} {P : E → ℂ[X]} {κ : E → ℝ}
    (hP : CoeffContDiffOn P U) (hκ : ContDiffOn ℝ ∞ κ U)
    (D : ℕ) (hD : ∀ y ∈ U, (P y).natDegree < D) :
    ContDiffOn ℝ ∞ (polynomialProfileFamily κ P) (U ×ˢ univ) := by
  exact (Real.contDiff_exp.comp_contDiffOn
    (((hκ.comp contDiffOn_fst (fun x (hx : x ∈ U ×ˢ (univ : Set ℝ)) => hx.1)).neg).mul
      contDiffOn_snd)).smul (hP.eval D hD)

theorem polynomialProfileFamily_eq_zero_of_polynomial_zero (κ : E → ℝ) (P : E → ℂ[X])
    {y : E} (hy : P y = 0) (s : ℝ) : polynomialProfileFamily κ P (y, s) = 0 := by
  simp [polynomialProfileFamily, hy]

end CalderonPatch.BoundaryLayer

open Polynomial Finset Set Filter Topology
open scoped ContDiff
namespace CalderonPatch.BoundaryLayer
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

@[expose] def polynomialSpatialDeriv (D : ℕ) (v : E) (P : E → ℂ[X]) (y : E) : ℂ[X] :=
  ∑ j ∈ range (D + 1), monomial j (fderiv ℝ (fun x => (P x).coeff j) y v)

theorem polynomialSpatialDeriv_natDegree_le (D : ℕ) (v : E) (P : E → ℂ[X]) (y : E) :
    (polynomialSpatialDeriv D v P y).natDegree ≤ D := by
  apply natDegree_sum_le_of_forall_le
  intro j hj
  exact (natDegree_monomial_le _).trans (by have := mem_range.mp hj; omega)

theorem CoeffContDiffOn.spatialDeriv {U : Set E} {P : E → ℂ[X]}
    (hP : CoeffContDiffOn P U) (hU : IsOpen U) (D : ℕ) (v : E) :
    CoeffContDiffOn (polynomialSpatialDeriv D v P) U := by
  apply CoeffContDiffOn.sum
  intro j hj
  apply CoeffContDiffOn.monomial
  exact ((hP j).fderiv_of_isOpen hU (by simp : (∞ : ℕ∞ω) + 1 ≤ ∞)).clm_apply contDiffOn_const

theorem polynomialSpatialDeriv_zero_outside (D : ℕ) (v : E) (P : E → ℂ[X])
    {K : Set E} (hK : IsClosed K) (hP0 : ∀ y ∉ K, P y = 0) {y : E} (hy : y ∉ K) :
    polynomialSpatialDeriv D v P y = 0 := by
  have he (j : ℕ) : (fun x => (P x).coeff j) =ᶠ[𝓝 y] (fun _ => (0 : ℂ)) := by
    filter_upwards [hK.isOpen_compl.mem_nhds hy] with x hx
    simp [hP0 x hx]
  have hd (j : ℕ) : fderiv ℝ (fun x => (P x).coeff j) y v = 0 := by
    rw [(he j).fderiv_eq]
    simp
  simp [polynomialSpatialDeriv, hd]

theorem fderiv_polynomial_eval_direction {U : Set E} (hU : IsOpen U)
    {P : E → ℂ[X]} (hP : CoeffContDiffOn P U) (D : ℕ)
    (hD : ∀ x ∈ U, (P x).natDegree ≤ D) {y : E} (hy : y ∈ U) (s : ℂ) (v : E) :
    fderiv ℝ (fun x => (P x).eval s) y v = (polynomialSpatialDeriv D v P y).eval s := by
  have he : (fun x => (P x).eval s) =ᶠ[𝓝 y]
      (fun x => ∑ j ∈ range (D + 1), s ^ j • (P x).coeff j) := by
    filter_upwards [hU.mem_nhds hy] with x hx
    simpa only [smul_eq_mul, mul_comm] using
      (P x).eval_eq_sum_range' (Nat.lt_succ_of_le (hD x hx)) s
  have hd : HasFDerivAt (fun x => ∑ j ∈ range (D + 1), s ^ j • (P x).coeff j)
      (∑ j ∈ range (D + 1), s ^ j • fderiv ℝ (fun x => (P x).coeff j) y) y := by
    apply HasFDerivAt.fun_sum
    intro j hj
    exact (((hP j y hy).contDiffAt (hU.mem_nhds hy)).differentiableAt (by simp)).hasFDerivAt.const_smul (s ^ j)
  rw [he.fderiv_eq, hd.fderiv]
  simp [polynomialSpatialDeriv, eval_finsetSum, ContinuousLinearMap.sum_apply, mul_comm]

end CalderonPatch.BoundaryLayer

open Polynomial
namespace CalderonPatch.BoundaryLayer

@[expose] def polynomialProfile (κ : ℝ) (p : ℂ[X]) (s : ℝ) : ℂ :=
  Real.exp (-κ * s) • p.eval (s : ℂ)

@[expose] def profileDerivative (κ : ℝ) (p : ℂ[X]) : ℂ[X] := derivative p - C (κ : ℂ) * p

theorem hasDerivAt_polynomialProfile (κ : ℝ) (p : ℂ[X]) (s : ℝ) :
    HasDerivAt (polynomialProfile κ p) (polynomialProfile κ (profileDerivative κ p) s) s := by
  have he : HasDerivAt (fun t : ℝ => Real.exp (-κ * t))
      ((-κ * Real.exp (-κ * s)) : ℝ) s := by
    convert ((hasDerivAt_id s).const_mul (-κ)).exp using 1 <;> simp [mul_comm]
  have hp := (p.hasDerivAt (s : ℂ)).comp_ofReal
  convert he.smul hp using 1
  · funext t
    simp only [polynomialProfile, Pi.smul_apply', neg_mul]
  · simp [polynomialProfile, profileDerivative, Complex.real_smul, mul_add, mul_sub]
    ring

theorem deriv_polynomialProfile (κ : ℝ) (p : ℂ[X]) :
    deriv (polynomialProfile κ p) = polynomialProfile κ (profileDerivative κ p) := by
  funext s
  exact (hasDerivAt_polynomialProfile κ p s).deriv

theorem secondOrder_polynomialProfile (κ : ℝ) (p : ℂ[X]) (s : ℝ) :
    -deriv (deriv (polynomialProfile κ p)) s + κ ^ 2 • polynomialProfile κ p s =
      polynomialProfile κ (C (2 * (κ : ℂ)) * derivative p - derivative (derivative p)) s := by
  rw [deriv_polynomialProfile, deriv_polynomialProfile]
  simp [polynomialProfile, profileDerivative, derivative_sub, derivative_C_mul,
    Complex.real_smul, Complex.ofReal_pow]
  ring

theorem zeroBoundaryProfile_equation (κ : ℝ) (hκ : κ ≠ 0) (p : ℂ[X]) (s : ℝ) :
    -deriv (deriv (polynomialProfile κ (polynomialTransport κ p))) s +
      κ ^ 2 • polynomialProfile κ (polynomialTransport κ p) s = polynomialProfile κ p s := by
  rw [secondOrder_polynomialProfile, polynomialTransport_equation κ hκ]

theorem zeroBoundaryProfile_zero (κ : ℝ) (p : ℂ[X]) :
    polynomialProfile κ (polynomialTransport κ p) 0 = 0 := by
  simp [polynomialProfile, polynomialTransport_zero]

theorem zeroBoundaryProfile_deriv_zero (κ : ℝ) (p : ℂ[X]) :
    deriv (polynomialProfile κ (polynomialTransport κ p)) 0 =
      (polynomialResolvent (2 * (κ : ℂ)) (p.natDegree + 1) p).eval 0 := by
  rw [deriv_polynomialProfile]
  simp [polynomialProfile, profileDerivative, polynomialTransport,
    polynomialPrimitive_derivative, polynomialPrimitive_zero]

end CalderonPatch.BoundaryLayer

open Polynomial Set Finset
open scoped ContDiff
namespace CalderonPatch.BoundaryLayer
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem CoeffContDiffOn.const (p : ℂ[X]) (U : Set E) : CoeffContDiffOn (fun _ => p) U :=
  fun _ => contDiffOn_const

theorem CoeffContDiffOn.mul {U : Set E} {P Q : E → ℂ[X]}
    (hP : CoeffContDiffOn P U) (hQ : CoeffContDiffOn Q U) :
    CoeffContDiffOn (fun x => P x * Q x) U := by
  intro j
  simp only [coeff_mul]
  exact ContDiffOn.sum (fun i _ => (hP i.1).mul (hQ i.2))

theorem CoeffContDiffOn.eval_const {U : Set E} {P : E → ℂ[X]}
    (hP : CoeffContDiffOn P U) (D : ℕ) (hD : ∀ x ∈ U, (P x).natDegree ≤ D) (s : ℝ) :
    ContDiffOn ℝ ∞ (fun x => (P x).eval (s : ℂ)) U := by
  have hs : ContDiffOn ℝ ∞
      (fun x : E => ∑ j ∈ range (D + 1), (P x).coeff j * (s : ℂ) ^ j) U := by
    apply ContDiffOn.sum
    intro j hj
    exact (hP j).mul contDiffOn_const
  apply hs.congr
  intro x hx
  exact (P x).eval_eq_sum_range' (Nat.lt_succ_of_le (hD x hx)) (s : ℂ)

@[expose] def profileSpatialDeriv (D : ℕ) (v : E) (κ : E → ℝ) (P : E → ℂ[X]) (y : E) : ℂ[X] :=
  polynomialSpatialDeriv D v P y - C (fderiv ℝ κ y v : ℂ) * X * P y

theorem profileSpatialDeriv_natDegree_le (D : ℕ) (v : E) (κ : E → ℝ) (P : E → ℂ[X])
    {y : E} (hD : (P y).natDegree ≤ D) : (profileSpatialDeriv D v κ P y).natDegree ≤ D + 1 := by
  apply (natDegree_sub_le _ _).trans
  apply max_le
  · exact (polynomialSpatialDeriv_natDegree_le D v P y).trans (Nat.le_succ D)
  · have hc : (C (fderiv ℝ κ y v : ℂ) * X).natDegree ≤ 1 :=
      (natDegree_C_mul_le _ _).trans natDegree_X_le
    have hm : (C (fderiv ℝ κ y v : ℂ) * X * P y).natDegree ≤
        (C (fderiv ℝ κ y v : ℂ) * X).natDegree + (P y).natDegree := natDegree_mul_le
    exact hm.trans (by omega)

theorem CoeffContDiffOn.profileSpatialDeriv {U : Set E} (hU : IsOpen U)
    {P : E → ℂ[X]} {κ : E → ℝ} (hP : CoeffContDiffOn P U) (hκ : ContDiffOn ℝ ∞ κ U)
    (D : ℕ) (v : E) : CoeffContDiffOn (profileSpatialDeriv D v κ P) U := by
  have hd := (hκ.fderiv_of_isOpen hU (by simp : (∞ : ℕ∞ω) + 1 ≤ ∞)).clm_apply
    (contDiffOn_const : ContDiffOn ℝ ∞ (fun _ : E => v) U)
  exact (hP.spatialDeriv hU D v).sub
    (((CoeffContDiffOn.const X U).C_mul (Complex.ofRealCLM.contDiff.comp_contDiffOn hd)).mul hP)

theorem profileSpatialDeriv_zero_outside (D : ℕ) (v : E) (κ : E → ℝ) (P : E → ℂ[X])
    {K : Set E} (hK : IsClosed K) (hP0 : ∀ x ∉ K, P x = 0) {y : E} (hy : y ∉ K) :
    profileSpatialDeriv D v κ P y = 0 := by
  simp [profileSpatialDeriv, polynomialSpatialDeriv_zero_outside D v P hK hP0 hy, hP0 y hy]

theorem fderiv_polynomialProfile_direction {U : Set E} (hU : IsOpen U)
    {P : E → ℂ[X]} {κ : E → ℝ} (hP : CoeffContDiffOn P U) (hκ : ContDiffOn ℝ ∞ κ U)
    (D : ℕ) (hD : ∀ x ∈ U, (P x).natDegree ≤ D) {y : E} (hy : y ∈ U) (s : ℝ) (v : E) :
    fderiv ℝ (fun x => polynomialProfile (κ x) (P x) s) y v =
      polynomialProfile (κ y) (profileSpatialDeriv D v κ P y) s := by
  have hk := ((hκ y hy).contDiffAt (hU.mem_nhds hy)).differentiableAt (by simp)
  have hp := ((hP.eval_const D hD s y hy).contDiffAt (hU.mem_nhds hy)).differentiableAt (by simp)
  have he : HasFDerivAt (fun x : E => Real.exp (-κ x * s))
      (Real.exp (-κ y * s) • s • -fderiv ℝ κ y) y := (hk.hasFDerivAt.neg.mul_const s).exp
  have heval : fderiv ℝ (fun x => Real.exp (-κ x * s)) y v =
      (-s * fderiv ℝ κ y v) * Real.exp (-κ y * s) := by
    rw [he.fderiv]
    simp
    ring
  unfold polynomialProfile
  rw [fderiv_fun_smul he.differentiableAt hp]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.smulRight_apply]
  rw [fderiv_polynomial_eval_direction hU hP D hD hy (s : ℂ) v, heval]
  simp [profileSpatialDeriv, Complex.real_smul]
  ring

end CalderonPatch.BoundaryLayer
