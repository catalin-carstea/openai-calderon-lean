import Proof.PolynomialDerivativeFields

noncomputable section
open Set MvPolynomial
open scoped ContDiff
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.AngularPolynomial

/-- The polynomial connection differentiates angular derivatives with the corresponding
    covector connection correction. -/
lemma polynomialConnection_partial_commutator (A : I → I → ℝ) (p : MvPolynomial I ℝ) (i : I) :
    polynomialConnectionAction A (pderiv i p) - pderiv i (polynomialConnectionAction A p) =
      ∑ a, C (A i a) * pderiv a p := by
  fin_cases i <;>
    simp [polynomialConnectionAction, Fin.sum_univ_three, pderiv_mul,
      pderiv_pderiv_comm (0:I) 1 p, pderiv_pderiv_comm (0:I) 2 p,
      pderiv_pderiv_comm (1:I) 2 p] <;> ring

lemma polynomialConnection_multiplication_commutator (A : I → I → ℝ)
    (hA : ∀ i j, A i j = -A j i) (p : MvPolynomial I ℝ) (i : I) :
    polynomialConnectionAction A (MvPolynomial.X i * p) - MvPolynomial.X i * polynomialConnectionAction A p =
      ∑ a, C (A i a) * (MvPolynomial.X a * p) := by
  have hd (a : I) : A a a = 0 := by have hh := hA a a; linarith
  fin_cases i <;>
    simp [polynomialConnectionAction, Fin.sum_univ_three, pderiv_mul, hd] <;>
    rw [hA 1 0, hA 2 0, hA 2 1] <;> simp only [map_neg] <;> ring

variable {ι : Type*} [Fintype ι]

lemma finitePolynomialField_partial (b : ι → MvPolynomial I ℝ) (c : X → ι → ℝ) (y : X) (i : I) :
    finitePolynomialField (fun t => pderiv i (b t)) c y = pderiv i (finitePolynomialField b c y) := by
  simp only [finitePolynomialField, map_sum, smul_eq_C_mul, pderiv_C_mul]

lemma finitePolynomialField_multiplication (b : ι → MvPolynomial I ℝ) (c : X → ι → ℝ) (y : X) (i : I) :
    finitePolynomialField (fun t => MvPolynomial.X i * b t) c y = MvPolynomial.X i * finitePolynomialField b c y := by
  simp only [finitePolynomialField, smul_eq_C_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro t _
  ring

/-- Covariant derivative with the additional lower tensor index of a polynomial covector. -/
def covectorPolynomialDerivative (g : MetricField) (e : Frame)
    (b : ι → I → MvPolynomial I ℝ) (c : X → ι → ℝ) (y a : X) (i : I) : MvPolynomial I ℝ :=
  covariantPolynomialDerivative g e (fun t => b t i) c y a -
    ∑ j, C (frameConnectionCoefficient g e y a i j) * finitePolynomialField (fun t => b t j) c y

lemma covectorPolynomialDerivative_partial (g : MetricField) (e : Frame)
    (b : ι → MvPolynomial I ℝ) (c : X → ι → ℝ) (y a : X) (i : I) :
    covectorPolynomialDerivative g e (fun t j => pderiv j (b t)) c y a i =
      pderiv i (covariantPolynomialDerivative g e b c y a) := by
  have hh := polynomialConnection_partial_commutator (frameConnectionCoefficient g e y a)
    (finitePolynomialField b c y) i
  simp only [covectorPolynomialDerivative, covariantPolynomialDerivative, finitePolynomialField_partial,
    finitePolynomialFieldDerivative, map_sum, smul_eq_C_mul, pderiv_C_mul, map_add]
  linear_combination hh

lemma covectorPolynomialDerivative_multiplication {Ω : Set X} (hΩ : IsOpen Ω) {K : ℝ}
    {g : MetricField} (h : Elliptic Ω K g) (hK : 0 < K) (e : Frame)
    (he : ∀ i, ContDiffOn ℝ ∞ (fun x => e x i) Ω)
    (hframe : ∀ x ∈ Ω, ∀ i j, metricPair g x (e x i) (e x j) = if i = j then 1 else 0)
    (b : ι → MvPolynomial I ℝ) (c : X → ι → ℝ) {y : X} (hy : y ∈ Ω) (a : X) (i : I) :
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

end ShrinkingSpheres
