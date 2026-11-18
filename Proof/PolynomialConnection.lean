import Proof.FrameConnection
import Proof.Archive.AngularCoefficient

noncomputable section
open Set MvPolynomial
open scoped ContDiff
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.AngularPolynomial

/-- The infinitesimal action on polynomial functions when frame coordinates are transported
    parallel. A_ij is the component along e_j of the covariant derivative of e_i. -/
def polynomialConnectionAction (A : I → I → ℝ) (p : MvPolynomial I ℝ) : MvPolynomial I ℝ :=
  ∑ i, ∑ j, C (-A i j) * (MvPolynomial.X i * pderiv j p)

lemma polynomialConnectionAction_skew (A : I → I → ℝ) (hA : ∀ i j, A i j = -A j i)
    (p q : MvPolynomial I ℝ) :
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

lemma polynomialConnectionAction_homogeneous (A : I → I → ℝ) {k : ℕ} (hk : 1 ≤ k)
    (p : MvPolynomial I ℝ) (hp : p.IsHomogeneous k) :
    (polynomialConnectionAction A p).IsHomogeneous k := by
  apply MvPolynomial.IsHomogeneous.sum
  intro i hi
  apply MvPolynomial.IsHomogeneous.sum
  intro j hj
  have hterm := ((isHomogeneous_X (R := ℝ) i).mul (hp.pderiv (i := j))).C_mul (-A i j)
  have hdegree : 1+(k-1) = k := by omega
  simpa only [hdegree] using hterm

lemma polynomialConnectionAction_harmonic (A : I → I → ℝ) (hA : ∀ i j, A i j = -A j i)
    (p : MvPolynomial I ℝ) (hp : laplacian p = 0) : laplacian (polynomialConnectionAction A p) = 0 := by
  have hd (i : I) : A i i = 0 := by have hh := hA i i; linarith
  simp only [polynomialConnectionAction, laplacian_sum, laplacian_C_mul, laplacian_X_mul,
    laplacian_pderiv, hp, map_zero, mul_zero, zero_add]
  simp only [Fin.sum_univ_three]
  rw [hd 0, hd 1, hd 2, hA 1 0, hA 2 0, hA 2 1,
    pderiv_pderiv_comm 1 0, pderiv_pderiv_comm 2 0, pderiv_pderiv_comm 2 1]
  simp only [map_neg, map_zero]
  ring

lemma actual_polynomialConnection_skew {Ω : Set X} (hΩ : IsOpen Ω) {K : ℝ} {g : MetricField}
    (h : Elliptic Ω K g) (hK : 0 < K) (e : Frame)
    (he : ∀ i, ContDiffOn ℝ ∞ (fun x => e x i) Ω)
    (hframe : ∀ x ∈ Ω, ∀ i j, metricPair g x (e x i) (e x j) = if i = j then 1 else 0)
    {y : X} (hy : y ∈ Ω) (a : X) (p q : MvPolynomial I ℝ) :
    fischerInner (polynomialConnectionAction (frameConnectionCoefficient g e y a) p) q =
      -fischerInner p (polynomialConnectionAction (frameConnectionCoefficient g e y a) q) :=
  polynomialConnectionAction_skew _ (frameConnection_skew hΩ h hK e he hframe hy a) p q

end ShrinkingSpheres
