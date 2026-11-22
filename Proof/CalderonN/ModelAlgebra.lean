module

public import Proof.CalderonN.FrameDuality
public import Proof.CalderonN.ProfileHessian
public import Proof.Archive.AngularCoefficient
public import Proof.Archive.RaisingCoercivity
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic

@[expose] public section

/- Port of ModelAlgebra.lean from the checked Proposition 5.3 release f308cb9d. -/
noncomputable section
open Set Filter MeasureTheory MvPolynomial
open scoped ContDiff Topology
namespace CalderonN
variable {n : ℕ}

open Set MvPolynomial

open OAI.AnisotropicCalderon.AngularPolynomial

/-- The degree k first-order model uses the actual frame components of d(log r). -/
def profileGradient (r : (X n) → ℝ) (e : (Frame n)) (y : (X n)) (i : (I n)) : ℝ :=
  fderiv ℝ (fun x => Real.log (r x)) y (e y i)

/-- Manuscript angular:convex-bound, with its pointwise coefficient c₁/β and arbitrary radius.
    The polynomial w supplies the horizontal derivatives of the same input component. -/
lemma profile_divergence_convex_bound (γ : (MetricField n)) (e : (Frame n)) (r : (X n) → ℝ) (y : (X n))
    (he : ∀ i j, metricPair γ y (e y i) (e y j) = if i = j then 1 else 0)
    {k : ℕ} (hk : 1 ≤ k) (v : MvPolynomial (I n) ℝ) (w : (I n) → MvPolynomial (I n) ℝ)
    (hv : v.IsHomogeneous k) (hw : ∀ i, (w i).IsHomogeneous k)
    (c₁ : ℝ) (hc₁ : 0 ≤ c₁) (hcβ : c₁ ≤ beta γ r y) (hβ : 0 < beta γ r y) :
    let f := profileGradient r e y
    let qp := weightedDerivativePlus k f v w
    let qm := weightedDerivativeMinus k f v w
    fischerInner (polynomialDivergence qp) (polynomialDivergence qp) ≤
      (1 - c₁ / beta γ r y) * (((k:ℝ)+(n:ℝ)-1) * ∑ i, fischerInner (qp i) (qp i)) +
      (c₁ / beta γ r y) * (2 * fischerInner (polynomialDivergence qm) (polynomialDivergence qm) +
        8 * (k:ℝ)^3 * (beta γ r y)^2 * fischerInner v v) := by
  have hnorm : ∑ i, (profileGradient r e y i)^2 ≤ (beta γ r y)^2 := (beta_sq γ e r y he).ge
  have hh := fischerInner_weightedDerivative_convex_bound hk (profileGradient r e y) v w hv hw
    (beta γ r y) (c₁ / beta γ r y) hnorm (div_nonneg hc₁ hβ.le) ((div_le_one hβ).2 hcβ)
  norm_num only [Fintype.card_fin] at hh
  convert hh using 1 <;> ring

/-- The two neighboring degree norms reduce to the Fischer expressions before integration.
    The Fock coefficients use the ambient dimension and the neighboring degrees. -/
lemma degree_fock_difference [NeZero n] (k : ℕ) (qp qm : (I n) → MvPolynomial (I n) ℝ)
    (hq : ∀ i, (qp i).IsHomogeneous (k+1)) (hΔ : ∀ i, laplacian (qp i) = 0) :
    normalizedFischerSquare (k+2) (C ((n:ℝ)+2*((k:ℝ)+1)) * harmonicRaising k qp) -
      normalizedFischerSquare k (polynomialDivergence qm) =
      (((n:ℝ)+2*((k:ℝ)+1)) * ((∑ i, fischerInner (qp i) (qp i)) +
        (∑ i, ∑ j, fischerInner (pderiv j (qp i)) (pderiv i (qp j))) -
        (4/(4*((k:ℝ)+(n:ℝ)/2))) * fischerInner (polynomialDivergence qp) (polynomialDivergence qp)) -
        ((n:ℝ)+2*(k:ℝ)) * fischerInner (polynomialDivergence qm) (polynomialDivergence qm)) /
      sphereNormalization n (k+1) := by
  have hh := normalizedFischer_fock_difference k qp qm hq hΔ
  norm_num only [Fintype.card_fin, Nat.cast_add, Nat.cast_one] at hh
  convert hh using 1 <;> ring

end CalderonN
