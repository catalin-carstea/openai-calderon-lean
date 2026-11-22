module

public import Proof.CalderonN.SmoothSphereRotationProjection
public import Proof.CalderonN.FiniteFockEnergy

import Mathlib.Tactic

@[expose] public section

/- Adapted from SphereElementaryCore and SphereDerivativeAdjoint in
   Proposition 5.3 release f308cb9d. -/
noncomputable section
open MvPolynomial
open scoped InnerProductSpace

namespace CalderonN

open OAI.AnisotropicCalderon SphereHarmonic AngularPolynomial

variable {n : ℕ} [NeZero n]

lemma pderiv_harmonicHomogeneous_succ (m : ℕ) (i : Fin n)
    (h : MvPolynomial (Fin n) ℝ) (hh : h ∈ harmonicHomogeneous n (m + 1)) :
    pderiv i h ∈ harmonicHomogeneous n m := by
  refine ⟨?_, ?_⟩
  · simpa only [Nat.add_sub_cancel] using hh.1.pderiv (i := i)
  · rw [laplacian_pderiv, hh.2, map_zero]

lemma single_harmonicHomogeneous (m : ℕ) (i : Fin n)
    (p : MvPolynomial (Fin n) ℝ) (hp : p ∈ harmonicHomogeneous n m) (j : Fin n) :
    (Pi.single i p : Fin n → MvPolynomial (Fin n) ℝ) j ∈ harmonicHomogeneous n m := by
  classical
  by_cases hji : j = i
  · subst j; simpa using hp
  · simpa [Pi.single_apply, hji] using (harmonicHomogeneous n m).zero_mem

/-- The sphere adjoint of the degree-lowering coordinate derivative. -/
def sphereDerivativeAdjoint (k : ℕ) (i : I n) (p : MvPolynomial (I n) ℝ) :
    MvPolynomial (I n) ℝ :=
  match k with
  | 0 => C (n : ℝ) * (MvPolynomial.X i * p)
  | m+1 => polynomialSphereRaising m (Pi.single i p)

theorem sphereDerivativeAdjoint_harmonicHomogeneous (k : ℕ) (i : I n)
    (p : MvPolynomial (I n) ℝ) (hp : p ∈ harmonicHomogeneous n k) :
    sphereDerivativeAdjoint k i p ∈ harmonicHomogeneous n (k+1) := by
  cases k with
  | zero =>
    rw [eq_C_of_mem_harmonicHomogeneous_zero hp]
    refine ⟨?_,?_⟩
    · simpa only [sphereDerivativeAdjoint, zero_add, Nat.zero_add, Nat.add_zero] using
        ((isHomogeneous_X (R := ℝ) i).mul (isHomogeneous_C (I n) (p.coeff 0))).C_mul (n : ℝ)
    · rw [sphereDerivativeAdjoint, laplacian_C_mul, laplacian_X_mul]
      simp [laplacian]
  | succ m =>
    have hq := fun j => single_harmonicHomogeneous (m+1) i p hp j
    refine ⟨?_,?_⟩
    · simpa only [sphereDerivativeAdjoint, polynomialSphereRaising, Nat.add_sub_cancel,
        Nat.cast_add, Nat.cast_one] using
        (harmonicRaising_isHomogeneous (k := m+1) (by omega) _ (fun j => (hq j).1)).C_mul
          ((n : ℝ) + 2 * ((m : ℝ) + 1))
    · have hL := laplacian_harmonicRaising (k := m+1) (Pi.single i p)
        (fun j => (hq j).1) (fun j => (hq j).2) (by
          have hn : (0 : ℝ) < n := by exact_mod_cast NeZero.pos n
          simp only [Fintype.card_fin]
          positivity)
      rw [Nat.add_sub_cancel] at hL
      simp only [sphereDerivativeAdjoint, polynomialSphereRaising, laplacian_C_mul, hL, mul_zero]

theorem sphereDerivativeAdjoint_inner_adjoint (hF : SphereFischerInner n) (k : ℕ)
    (i : I n) (p h : MvPolynomial (I n) ℝ)
    (hp : p ∈ harmonicHomogeneous n k) (hh : h ∈ harmonicHomogeneous n (k+1)) :
    ⟪polynomialSphereL2 (sphereDerivativeAdjoint k i p),polynomialSphereL2 h⟫_ℝ =
      ⟪polynomialSphereL2 p,polynomialSphereL2 (pderiv i h)⟫_ℝ := by
  rw [hF (k+1) _ h (sphereDerivativeAdjoint_harmonicHomogeneous k i p hp) hh,
    hF k p _ hp (pderiv_harmonicHomogeneous_succ k i h hh)]
  cases k with
  | zero =>
    simp only [sphereDerivativeAdjoint, normalizedFischerInner, fischerInner_C_mul_left,
      fischerInner_X_mul_left, Fintype.card_fin, sphereNormalization_succ, sphereNormalization_zero,
      Nat.cast_zero, mul_zero, add_zero, mul_one, div_one]
    have hn : (n : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne n
    field_simp
  | succ m =>
    have hadj := normalizedFischer_raising_adjoint m (Pi.single i p) h hh.2
    rw [show sphereDerivativeAdjoint (m+1) i p = polynomialSphereRaising m (Pi.single i p) from rfl]
    simp only [Fintype.card_fin, Nat.cast_add, Nat.cast_one] at hadj
    change normalizedFischerInner (m+2) (C ((n:ℝ)+2*((m:ℝ)+1)) * _) h = _
    rw [hadj]
    classical
    have he (j : I n) :
        normalizedFischerInner (m+1) ((Pi.single i p : I n → MvPolynomial (I n) ℝ) j) (pderiv j h) =
          if j = i then normalizedFischerInner (m+1) p (pderiv j h) else 0 := by
      by_cases hj : j = i <;> simp [Pi.single_apply, hj, normalizedFischerInner, fischerInner_zero_left]
    simp only [he, Finset.sum_ite_eq', Finset.mem_univ, if_true]

lemma sphereDerivativeAdjoint_C_mul (k : ℕ) (i : I n) (r : ℝ) (p : MvPolynomial (I n) ℝ) :
    sphereDerivativeAdjoint k i (C r*p) = C r*sphereDerivativeAdjoint k i p := by
  cases k with
  | zero => simp only [sphereDerivativeAdjoint]; ring
  | succ m =>
    have h : (Pi.single i (C r*p) : I n → MvPolynomial (I n) ℝ) =
        fun j => C r * (Pi.single i p : I n → MvPolynomial (I n) ℝ) j := by
      funext j
      by_cases hij : j = i <;> simp [Pi.single_apply, hij]
    simp only [sphereDerivativeAdjoint, h, polynomialSphereRaising_C_mul_family]

lemma sphereDerivativeAdjoint_add (k : ℕ) (i : I n) (p q : MvPolynomial (I n) ℝ) :
    sphereDerivativeAdjoint k i (p+q) = sphereDerivativeAdjoint k i p + sphereDerivativeAdjoint k i q := by
  cases k with
  | zero => simp only [sphereDerivativeAdjoint]; ring
  | succ m =>
    have h : (Pi.single i (p+q) : I n → MvPolynomial (I n) ℝ) =
        fun j => Pi.single i p j + Pi.single i q j := by
      funext j
      by_cases hij : j = i <;> simp [Pi.single_apply, hij]
    simp only [sphereDerivativeAdjoint, h, polynomialSphereRaising, harmonicRaising,
      polynomialRaising, polynomialDivergence, map_add, mul_add, Finset.sum_add_distrib]
    ring

lemma sphereDerivativeAdjoint_zero (k : ℕ) (i : I n) :
    sphereDerivativeAdjoint k i 0 = 0 := by
  have h := sphereDerivativeAdjoint_C_mul k i 0 0
  simpa only [map_zero, zero_mul] using h

end CalderonN
