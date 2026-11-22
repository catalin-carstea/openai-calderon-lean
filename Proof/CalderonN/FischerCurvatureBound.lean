module

public import Proof.CalderonN.PolynomialConnection
import Mathlib.Tactic

public section

/- Fischer curvature contraction from the released Proposition 5.3.
   The matrix-form bound now keeps the number of curvature indices explicit. -/
noncomputable section
open MvPolynomial
namespace CalderonN
open OAI.AnisotropicCalderon.AngularPolynomial

variable {n : ℕ}

lemma fischer_matrix_form_bound {J : Type*} [Fintype J] (A : J → J → ℝ)
    (B : ℝ) (hB : 0 ≤ B) (hA : ∀ i j, |A i j| ≤ B) (q : J → MvPolynomial (I n) ℝ) :
    |∑ i, ∑ j, A i j * fischerInner (q i) (q j)| ≤
      (Fintype.card J : ℝ) * B * ∑ i, fischerInner (q i) (q i) := by
  have hpoint (i j : J) : |A i j * fischerInner (q i) (q j)| ≤
      (B/2)*(fischerInner (q i) (q i) + fischerInner (q j) (q j)) := by
    rw [abs_mul]
    calc
      _ ≤ B * ((fischerInner (q i) (q i) + fischerInner (q j) (q j))/2) :=
        mul_le_mul (hA i j) (abs_fischerInner_le _ _) (abs_nonneg _) hB
      _ = _ := by ring
  calc
    _ ≤ ∑ i, |∑ j, A i j * fischerInner (q i) (q j)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, ∑ j, |A i j * fischerInner (q i) (q j)| :=
      Finset.sum_le_sum (fun i _ => Finset.abs_sum_le_sum_abs _ _)
    _ ≤ ∑ i, ∑ j, (B/2)*(fischerInner (q i) (q i) + fischerInner (q j) (q j)) :=
      Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ => hpoint i j))
    _ = _ := by
      simp only [mul_add, Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const,
        Finset.card_univ, nsmul_eq_mul]
      ring

lemma fischerInner_connectionAction (A : (I n) → (I n) → ℝ) (p q : MvPolynomial (I n) ℝ) :
    fischerInner p (polynomialConnectionAction A q) =
      ∑ a, ∑ b, (-A a b) * fischerInner (pderiv a p) (pderiv b q) := by
  simp only [polynomialConnectionAction, fischerInner_sum_right, fischerInner_C_mul_right,
    ← fischerInner_pderiv_left]

@[expose] def coefficientCurvatureContraction (R : (I n) → (I n) → (I n) → (I n) → ℝ) (p : MvPolynomial (I n) ℝ) : ℝ :=
  ∑ i, ∑ j, fischerInner (pderiv i p)
    (polynomialConnectionAction (R i j) (pderiv j p) - ∑ a, C (R i j j a) * pderiv a p)

lemma coefficientCurvatureContraction_expansion (R : (I n) → (I n) → (I n) → (I n) → ℝ) (p : MvPolynomial (I n) ℝ) :
    coefficientCurvatureContraction R p =
      (∑ i, ∑ j, ∑ a, ∑ b, (-R i j a b) *
        fischerInner (pderiv a (pderiv i p)) (pderiv b (pderiv j p))) -
      (∑ i, ∑ a, (∑ j, R i j j a) * fischerInner (pderiv i p) (pderiv a p)) := by
  simp only [coefficientCurvatureContraction, fischerInner_sub_right, fischerInner_connectionAction,
    fischerInner_sum_right, fischerInner_C_mul_right, Finset.sum_sub_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_comm]
  simp only [Finset.sum_mul]

lemma sum_fischer_second_derivatives {k : ℕ} (p : MvPolynomial (I n) ℝ) (hp : p.IsHomogeneous k) :
    (∑ i, ∑ a, fischerInner (pderiv a (pderiv i p)) (pderiv a (pderiv i p))) =
      ((k-1 : ℕ) : ℝ) * (k : ℝ) * fischerInner p p := by
  simp_rw [sum_fischerInner_pderiv_self (hp.pderiv)]
  rw [← Finset.mul_sum, sum_fischerInner_pderiv_self hp]
  ring

/-- The full covector curvature form has a degree-squared bound. This finite Fischer
    estimate needs only a bound for the actual curvature coefficients. -/
theorem coefficientCurvatureContraction_bound (R : (I n) → (I n) → (I n) → (I n) → ℝ)
    (B : ℝ) (hB : 0 ≤ B) (hR : ∀ i j a b, |R i j a b| ≤ B)
    {k : ℕ} (hk : 1 ≤ k) (p : MvPolynomial (I n) ℝ) (hp : p.IsHomogeneous k) :
    |coefficientCurvatureContraction R p| ≤ (n : ℝ)^2*B*(k : ℝ)^2*fischerInner p p := by
  have hsecond := fischer_matrix_form_bound
    (fun s t : (I n) × (I n) => -R s.1 t.1 s.2 t.2) B hB
    (fun s t => by simpa only [abs_neg] using hR s.1 t.1 s.2 t.2)
    (fun s : (I n) × (I n) => pderiv s.2 (pderiv s.1 p))
  simp only [Fintype.sum_prod_type, Fintype.card_prod, Fintype.card_fin] at hsecond
  have hswap : (∑ i, ∑ j, ∑ a, ∑ b, (-R i j a b) *
      fischerInner (pderiv a (pderiv i p)) (pderiv b (pderiv j p))) =
      (∑ i, ∑ a, ∑ j, ∑ b, (-R i j a b) *
        fischerInner (pderiv a (pderiv i p)) (pderiv b (pderiv j p))) := by
    apply Finset.sum_congr rfl
    intro i _
    exact Finset.sum_comm
  have hbaseCoeff (i a : (I n)) : |∑ j, R i j j a| ≤ (n : ℝ)*B := by
    calc
      _ ≤ ∑ j, |R i j j a| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _j : (I n), B := Finset.sum_le_sum (fun j _ => hR i j j a)
      _ = _ := by simp [I, nsmul_eq_mul]
  have hbase := fischer_matrix_form_bound (fun i a : (I n) => ∑ j, R i j j a) ((n : ℝ)*B)
    (by positivity) hbaseCoeff (fun i => pderiv i p)
  simp only [Fintype.card_fin, sum_fischerInner_pderiv_self hp] at hbase
  rw [sum_fischer_second_derivatives p hp, Nat.cast_sub hk, Nat.cast_one] at hsecond
  rw [coefficientCurvatureContraction_expansion]
  calc
    _ ≤ |∑ i, ∑ j, ∑ a, ∑ b, (-R i j a b) *
        fischerInner (pderiv a (pderiv i p)) (pderiv b (pderiv j p))| +
        |∑ i, ∑ a, (∑ j, R i j j a) * fischerInner (pderiv i p) (pderiv a p)| := abs_sub _ _
    _ ≤ ((n*n : ℕ) : ℝ)*B*(((k : ℝ)-1)*(k : ℝ)*fischerInner p p) +
        (n : ℝ)*((n : ℝ)*B)*((k : ℝ)*fischerInner p p) := by
      rw [hswap]
      exact add_le_add hsecond hbase
    _ = _ := by push_cast; ring

end CalderonN
