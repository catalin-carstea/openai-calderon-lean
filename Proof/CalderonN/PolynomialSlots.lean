module

public import Proof.CalderonN.PolynomialDerivativeFields
import Mathlib.Tactic

@[expose] public section

/- Coordinate-slot commutators from Proposition 5.3, generalized via sums. -/
noncomputable section
open Set MvPolynomial
open scoped ContDiff
namespace CalderonN
open OAI.AnisotropicCalderon.AngularPolynomial

variable {n : ℕ}

/-- The polynomial connection differentiates angular derivatives with the corresponding
    covector connection correction. -/
lemma polynomialConnection_partial_commutator (A : (I n) → (I n) → ℝ) (p : MvPolynomial (I n) ℝ) (i : (I n)) :
    polynomialConnectionAction A (pderiv i p) - pderiv i (polynomialConnectionAction A p) =
      ∑ a, C (A i a) * pderiv a p := by
  have hcomm (j : (I n)) := pderiv_pderiv_comm i j p
  simp only [polynomialConnectionAction, map_sum, pderiv_C_mul]
  simp only [pderiv_mul, pderiv_X, Pi.single_apply, ite_mul, one_mul, zero_mul, hcomm,
    mul_add, Finset.sum_add_distrib]
  simp only [mul_ite, mul_zero, map_neg, neg_mul]
  have hdelta (a : I n) :
      (∑ b : I n, if a = i then -(C (A a b) * pderiv b p) else 0) =
        if a = i then -(∑ b : I n, C (A a b) * pderiv b p) else 0 := by
    by_cases ha : a = i <;> simp [ha, Finset.sum_neg_distrib]
  simp only [hdelta, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  abel

lemma polynomialConnection_multiplication_commutator (A : (I n) → (I n) → ℝ)
    (hA : ∀ i j, A i j = -A j i) (p : MvPolynomial (I n) ℝ) (i : (I n)) :
    polynomialConnectionAction A (MvPolynomial.X i * p) - MvPolynomial.X i * polynomialConnectionAction A p =
      ∑ a, C (A i a) * (MvPolynomial.X a * p) := by
  have hterm (a : (I n)) :
      (∑ j, C (-A a j) * (MvPolynomial.X a * pderiv j (MvPolynomial.X i * p))) =
        C (A i a) * (MvPolynomial.X a * p) +
          MvPolynomial.X i * (∑ j, C (-A a j) * (MvPolynomial.X a * pderiv j p)) := by
    simp only [pderiv_mul, pderiv_X, Pi.single_apply, ite_mul, one_mul, zero_mul,
      mul_add, Finset.sum_add_distrib]
    simp only [mul_ite, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
    rw [hA a i, neg_neg, Finset.mul_sum]
    congr 1
    exact Finset.sum_congr rfl fun j _ => by ring
  simp only [polynomialConnectionAction, hterm, Finset.sum_add_distrib, ← Finset.mul_sum]
  abel

variable {ι : Type*} [Fintype ι]

lemma finitePolynomialField_partial (b : ι → MvPolynomial (I n) ℝ) (c : (X n) → ι → ℝ) (y : (X n)) (i : (I n)) :
    finitePolynomialField (fun t => pderiv i (b t)) c y = pderiv i (finitePolynomialField b c y) := by
  simp only [finitePolynomialField, map_sum, smul_eq_C_mul, pderiv_C_mul]

lemma finitePolynomialField_multiplication (b : ι → MvPolynomial (I n) ℝ) (c : (X n) → ι → ℝ) (y : (X n)) (i : (I n)) :
    finitePolynomialField (fun t => MvPolynomial.X i * b t) c y = MvPolynomial.X i * finitePolynomialField b c y := by
  simp only [finitePolynomialField, smul_eq_C_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro t _
  ring

/-- Covariant derivative with the additional lower tensor index of a polynomial covector. -/
def covectorPolynomialDerivative (g : (MetricField n)) (e : (Frame n))
    (b : ι → (I n) → MvPolynomial (I n) ℝ) (c : (X n) → ι → ℝ) (y a : (X n)) (i : (I n)) : MvPolynomial (I n) ℝ :=
  covariantPolynomialDerivative g e (fun t => b t i) c y a -
    ∑ j, C (frameConnectionCoefficient g e y a i j) * finitePolynomialField (fun t => b t j) c y

lemma covectorPolynomialDerivative_partial (g : (MetricField n)) (e : (Frame n))
    (b : ι → MvPolynomial (I n) ℝ) (c : (X n) → ι → ℝ) (y a : (X n)) (i : (I n)) :
    covectorPolynomialDerivative g e (fun t j => pderiv j (b t)) c y a i =
      pderiv i (covariantPolynomialDerivative g e b c y a) := by
  have hh := polynomialConnection_partial_commutator (frameConnectionCoefficient g e y a)
    (finitePolynomialField b c y) i
  simp only [covectorPolynomialDerivative, covariantPolynomialDerivative, finitePolynomialField_partial,
    finitePolynomialFieldDerivative, map_sum, smul_eq_C_mul, pderiv_C_mul, map_add]
  linear_combination hh

lemma covectorPolynomialDerivative_multiplication {Ω : Set (X n)} (hΩ : IsOpen Ω) {K : ℝ}
    {g : (MetricField n)} (h : Elliptic Ω K g) (hK : 0 < K) (e : (Frame n))
    (he : ∀ i, ContDiffOn ℝ ∞ (fun x => e x i) Ω)
    (hframe : ∀ x ∈ Ω, ∀ i j, metricPair g x (e x i) (e x j) = if i = j then 1 else 0)
    (b : ι → MvPolynomial (I n) ℝ) (c : (X n) → ι → ℝ) {y : (X n)} (hy : y ∈ Ω) (a : (X n)) (i : (I n)) :
    covectorPolynomialDerivative g e (fun t j => MvPolynomial.X j * b t) c y a i =
      MvPolynomial.X i * covariantPolynomialDerivative g e b c y a := by
  have hh := polynomialConnection_multiplication_commutator (frameConnectionCoefficient g e y a)
    (frameConnection_skew hΩ h hK e he hframe hy a) (finitePolynomialField b c y) i
  have hmul : finitePolynomialFieldDerivative (fun t => MvPolynomial.X i * b t) c y a =
      MvPolynomial.X i * finitePolynomialFieldDerivative b c y a :=
    finitePolynomialField_multiplication b (fun _ => fderiv ℝ c y a) y i
  simp only [covectorPolynomialDerivative, covariantPolynomialDerivative, finitePolynomialField_multiplication,
    hmul, mul_add]
  linear_combination hh

end CalderonN
