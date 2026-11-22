module

public import Proof.CalderonN.MetricConnection
public import Proof.Archive.AngularCoefficient
import Mathlib.Tactic

public section

/- Infinitesimal rotation on the homogeneous coefficient space in the
   Proposition 5.3 proof. Harmonicity follows from skew-symmetry for all n. -/
noncomputable section
open Set MvPolynomial
open scoped ContDiff
namespace CalderonN
open OAI.AnisotropicCalderon.AngularPolynomial

variable {n : ℕ}

/-- The infinitesimal action on polynomial functions when frame coordinates are transported
    parallel. A_ij is the component along e_j of the covariant derivative of e_i. -/
@[expose] def polynomialConnectionAction (A : (I n) → (I n) → ℝ) (p : MvPolynomial (I n) ℝ) : MvPolynomial (I n) ℝ :=
  ∑ i, ∑ j, C (-A i j) * (MvPolynomial.X i * pderiv j p)

lemma polynomialConnectionAction_skew (A : (I n) → (I n) → ℝ) (hA : ∀ i j, A i j = -A j i)
    (p q : MvPolynomial (I n) ℝ) :
    fischerInner (polynomialConnectionAction A p) q =
      -fischerInner p (polynomialConnectionAction A q) := by
  simp only [polynomialConnectionAction, fischerInner_sum_left, fischerInner_sum_right,
    fischerInner_C_mul_left, fischerInner_C_mul_right,
    fischerInner_X_mul_left, ← fischerInner_pderiv_left, ← Finset.sum_neg_distrib]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [hA j i]
  ring

lemma polynomialConnectionAction_homogeneous (A : (I n) → (I n) → ℝ) {k : ℕ} (hk : 1 ≤ k)
    (p : MvPolynomial (I n) ℝ) (hp : p.IsHomogeneous k) :
    (polynomialConnectionAction A p).IsHomogeneous k := by
  apply MvPolynomial.IsHomogeneous.sum
  intro i hi
  apply MvPolynomial.IsHomogeneous.sum
  intro j hj
  have hterm := ((isHomogeneous_X (R := ℝ) i).mul (hp.pderiv (i := j))).C_mul (-A i j)
  have hdegree : 1+(k-1) = k := by omega
  simpa only [hdegree] using hterm

lemma polynomialConnectionAction_harmonic (A : (I n) → (I n) → ℝ) (hA : ∀ i j, A i j = -A j i)
    (p : MvPolynomial (I n) ℝ) (hp : laplacian p = 0) : laplacian (polynomialConnectionAction A p) = 0 := by
  simp only [polynomialConnectionAction, laplacian_sum, laplacian_C_mul, laplacian_X_mul,
    laplacian_pderiv, hp, map_zero, mul_zero, zero_add]
  let S := ∑ i : (I n), ∑ j : (I n), C (-A i j) * (2 * pderiv i (pderiv j p))
  change S = 0
  have hs : S = -S := by
    unfold S
    conv_lhs =>
      rw [Finset.sum_comm (f := fun i j => C (-A i j) * (2 * pderiv i (pderiv j p)))]
    simp only [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by
      rw [hA j i, neg_neg, pderiv_pderiv_comm j i, map_neg]
      ring
  have hz : S + S = 0 := by
    nth_rw 1 [hs]
    exact neg_add_cancel S
  rw [← two_mul, mul_eq_zero] at hz
  exact hz.resolve_left two_ne_zero

lemma actual_polynomialConnection_skew {Ω : Set (X n)} (hΩ : IsOpen Ω) {K : ℝ} {g : (MetricField n)}
    (h : Elliptic Ω K g) (hK : 0 < K) (e : (Frame n))
    (he : ∀ i, ContDiffOn ℝ ∞ (fun x => e x i) Ω)
    (hframe : ∀ x ∈ Ω, ∀ i j, metricPair g x (e x i) (e x j) = if i = j then 1 else 0)
    {y : (X n)} (hy : y ∈ Ω) (a : (X n)) (p q : MvPolynomial (I n) ℝ) :
    fischerInner (polynomialConnectionAction (frameConnectionCoefficient g e y a) p) q =
      -fischerInner p (polynomialConnectionAction (frameConnectionCoefficient g e y a) q) :=
  polynomialConnectionAction_skew _ (frameConnection_skew hΩ h hK e he hframe hy a) p q

end CalderonN
