module

public import Proof.CalderonN.SphereHarmonicBridge
import Mathlib.Tactic

@[expose] public section

/- The polynomial Casimir in f308cb9d, with finite-index sums in place of
   its expansion of the three coordinate directions. -/
noncomputable section
open MvPolynomial
open scoped InnerProductSpace

namespace CalderonN
open OAI.AnisotropicCalderon AngularPolynomial SphereHarmonic

variable {n : ℕ}

def polynomialRotation (i j : Fin n) (p : MvPolynomial (Fin n) ℝ) :
    MvPolynomial (Fin n) ℝ := MvPolynomial.X i * pderiv j p - MvPolynomial.X j * pderiv i p

def polynomialEuler (p : MvPolynomial (Fin n) ℝ) : MvPolynomial (Fin n) ℝ :=
  ∑ i : Fin n, MvPolynomial.X i * pderiv i p

def polynomialCasimir (p : MvPolynomial (Fin n) ℝ) : MvPolynomial (Fin n) ℝ :=
  C (-(1/2 : ℝ)) * ∑ i : Fin n, ∑ j : Fin n,
    polynomialRotation i j (polynomialRotation i j p)

private theorem polynomialEuler_twice (p : MvPolynomial (Fin n) ℝ) :
    polynomialEuler (polynomialEuler p) =
      polynomialEuler p +
        ∑ i : Fin n, ∑ j : Fin n, MvPolynomial.X i * MvPolynomial.X j * pderiv i (pderiv j p) := by
  classical
  conv_lhs =>
    unfold polynomialEuler
  simp only [map_sum, Finset.mul_sum, pderiv_mul, mul_add, Finset.sum_add_distrib,
    pderiv_X, Pi.single_apply, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq',
    Finset.mem_univ, ite_true, mul_assoc]
  simp [polynomialEuler]

private def rotationSquareTerm (p : MvPolynomial (Fin n) ℝ) (i j : Fin n) :
    MvPolynomial (Fin n) ℝ :=
  MvPolynomial.X i ^ 2 * pderiv j (pderiv j p) -
    MvPolynomial.X i * MvPolynomial.X j * pderiv i (pderiv j p) -
    MvPolynomial.X i * pderiv i p +
    if i = j then MvPolynomial.X i * pderiv i p else 0

private theorem polynomialRotation_twice (p : MvPolynomial (Fin n) ℝ) (i j : Fin n) :
    polynomialRotation i j (polynomialRotation i j p) =
      rotationSquareTerm p i j + rotationSquareTerm p j i := by
  by_cases hij : i = j
  · subst j
    simp [polynomialRotation, rotationSquareTerm, pow_two]
  · simp only [polynomialRotation, rotationSquareTerm, hij, Ne.symm hij, ite_false, add_zero,
      map_sub, pderiv_mul, pderiv_X_self, pderiv_X, Pi.single_apply,
      zero_mul, zero_add, one_mul]
    rw [pderiv_pderiv_comm j i p]
    ring

private theorem sum_rotationSquareTerm (p : MvPolynomial (Fin n) ℝ) :
    (∑ i : Fin n, ∑ j : Fin n, rotationSquareTerm p i j) =
      radiusSq * laplacian p - polynomialEuler (polynomialEuler p) -
      C ((n : ℝ) - 2) * polynomialEuler p := by
  classical
  rw [polynomialEuler_twice]
  simp only [rotationSquareTerm, Finset.sum_add_distrib, Finset.sum_sub_distrib,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, Finset.sum_ite_eq, Finset.mem_univ,
    ite_true, ← Finset.mul_sum, ← Finset.sum_mul, ← Finset.smul_sum]
  rw [nsmul_eq_mul, ← map_natCast C]
  simp only [map_sub, map_ofNat]
  unfold polynomialEuler radiusSq laplacian
  ring

theorem sum_double_rotation_eq (p : MvPolynomial (Fin n) ℝ) :
    (∑ i : Fin n, ∑ j : Fin n, polynomialRotation i j (polynomialRotation i j p)) =
      2 * (radiusSq * laplacian p - polynomialEuler (polynomialEuler p) -
        C ((n : ℝ) - 2) * polynomialEuler p) := by
  simp only [polynomialRotation_twice, Finset.sum_add_distrib]
  rw [Finset.sum_comm (f := fun i j => rotationSquareTerm p j i), sum_rotationSquareTerm]
  ring

lemma polynomialEuler_C_mul (a : ℝ) (p : MvPolynomial (Fin n) ℝ) :
    polynomialEuler (C a * p) = C a * polynomialEuler p := by
  simp [polynomialEuler, Finset.mul_sum, mul_left_comm]

lemma polynomialEuler_homogeneous (k : ℕ) (p : MvPolynomial (Fin n) ℝ)
    (hp : p.IsHomogeneous k) : polynomialEuler p = C (k : ℝ) * p := by
  simpa [polynomialEuler, nsmul_eq_mul] using hp.sum_X_mul_pderiv

theorem polynomialCasimir_harmonic (k : ℕ) (p : MvPolynomial (Fin n) ℝ)
    (hp : p ∈ harmonicHomogeneous n k) :
    polynomialCasimir p = C ((k : ℝ) * ((k : ℝ) + n - 2)) * p := by
  rw [polynomialCasimir, sum_double_rotation_eq, polynomialEuler_homogeneous k p hp.1,
    polynomialEuler_C_mul, polynomialEuler_homogeneous k p hp.1, hp.2]
  have h2 : C (-(1/2 : ℝ)) * (2 : MvPolynomial (Fin n) ℝ) = -1 := by
    calc
      _ = C (-(1/2 : ℝ) * 2) := by simp only [map_mul, map_ofNat]
      _ = -1 := by norm_num
  rw [← mul_assoc, h2]
  simp only [map_ofNat, map_mul, map_sub, map_add]
  ring

end CalderonN
