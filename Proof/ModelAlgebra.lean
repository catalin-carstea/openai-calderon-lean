import Proof.FrameDuality
import Proof.ProfileHessian
import Proof.Archive.AngularCoefficient
import Proof.Archive.RaisingCoercivity

noncomputable section
open Set MvPolynomial
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.AngularPolynomial

/-- The degree k first-order model uses the actual frame components of d(log r). -/
def profileGradient (r : X → ℝ) (e : Frame) (y : X) (i : I) : ℝ :=
  fderiv ℝ (fun x => Real.log (r x)) y (e y i)

/-- Manuscript angular:convex-bound, with its pointwise coefficient c₁/β and arbitrary radius.
    The polynomial w supplies the horizontal derivatives of the same input component. -/
lemma profile_divergence_convex_bound (γ : MetricField) (e : Frame) (r : X → ℝ) (y : X)
    (he : ∀ i j, metricPair γ y (e y i) (e y j) = if i = j then 1 else 0)
    {k : ℕ} (hk : 1 ≤ k) (v : MvPolynomial I ℝ) (w : I → MvPolynomial I ℝ)
    (hv : v.IsHomogeneous k) (hw : ∀ i, (w i).IsHomogeneous k)
    (c₁ : ℝ) (hc₁ : 0 ≤ c₁) (hcβ : c₁ ≤ beta γ r y) (hβ : 0 < beta γ r y) :
    let f := profileGradient r e y
    let qp := weightedDerivativePlus k f v w
    let qm := weightedDerivativeMinus k f v w
    fischerInner (polynomialDivergence qp) (polynomialDivergence qp) ≤
      (1 - c₁ / beta γ r y) * (((k:ℝ)+2) * ∑ i, fischerInner (qp i) (qp i)) +
      (c₁ / beta γ r y) * (2 * fischerInner (polynomialDivergence qm) (polynomialDivergence qm) +
        8 * (k:ℝ)^3 * (beta γ r y)^2 * fischerInner v v) := by
  have hnorm : ∑ i, (profileGradient r e y i)^2 ≤ (beta γ r y)^2 := (beta_sq γ e r y he).ge
  have hh := fischerInner_weightedDerivative_convex_bound hk (profileGradient r e y) v w hv hw
    (beta γ r y) (c₁ / beta γ r y) hnorm (div_nonneg hc₁ hβ.le) ((div_le_one hβ).2 hcβ)
  norm_num only [Fintype.card_fin] at hh
  convert hh using 1 <;> ring

/-- The two neighboring degree norms reduce to the Fischer expressions before integration.
    This is the supplied Fock calculation specialized only to dimension three. -/
lemma degree_fock_difference (k : ℕ) (qp qm : I → MvPolynomial I ℝ)
    (hq : ∀ i, (qp i).IsHomogeneous (k+1)) (hΔ : ∀ i, laplacian (qp i) = 0) :
    normalizedFischerSquare (k+2) (C (2*(k:ℝ)+5) * harmonicRaising k qp) -
      normalizedFischerSquare k (polynomialDivergence qm) =
      ((2*(k:ℝ)+5) * ((∑ i, fischerInner (qp i) (qp i)) +
        (∑ i, ∑ j, fischerInner (pderiv j (qp i)) (pderiv i (qp j))) -
        (4/(4*(k:ℝ)+6)) * fischerInner (polynomialDivergence qp) (polynomialDivergence qp)) -
        (2*(k:ℝ)+3) * fischerInner (polynomialDivergence qm) (polynomialDivergence qm)) /
      sphereNormalization 3 (k+1) := by
  have hh := normalizedFischer_fock_difference k qp qm hq hΔ
  norm_num only [Fintype.card_fin, Nat.cast_add, Nat.cast_one] at hh
  convert hh using 1 <;> ring

end ShrinkingSpheres
