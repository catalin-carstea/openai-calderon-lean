module

public import Proof.CalderonN.MetricSmooth
public import Proof.CalderonN.Localization
import Mathlib.Tactic

@[expose] public section

/- Port of PolynomialDerivativeFields.lean from the checked Proposition 5.3 release f308cb9d. -/
noncomputable section
open Set Filter MeasureTheory MvPolynomial
open scoped ContDiff Topology
namespace CalderonN
variable {n : ℕ}

open OAI.AnisotropicCalderon.AngularPolynomial

variable {ι : Type*} [Fintype ι]

/-- Fixed polynomial family containing a field and the finitely many polynomial connection
    terms in its derivative. -/
def derivativePolynomialFamily (b : ι → MvPolynomial (I n) ℝ) : ι ⊕ ((I n) × (I n) × ι) → MvPolynomial (I n) ℝ
  | .inl j => b j
  | .inr a => MvPolynomial.X a.1 * pderiv a.2.1 (b a.2.2)

def derivativeCoefficientFamily (g : (MetricField n)) (e : (Frame n)) (c : (X n) → ι → ℝ) (V : (X n) → (X n))
    (x : (X n)) : ι ⊕ ((I n) × (I n) × ι) → ℝ
  | .inl j => fderiv ℝ c x (V x) j
  | .inr a => -frameConnectionCoefficient g e x (V x) a.1 a.2.1 * c x a.2.2

lemma covariantPolynomialDerivative_eq_augmented (g : (MetricField n)) (e : (Frame n))
    (b : ι → MvPolynomial (I n) ℝ) (c : (X n) → ι → ℝ) (V : (X n) → (X n)) (x : (X n)) :
    covariantPolynomialDerivative g e b c x (V x) =
      finitePolynomialField (derivativePolynomialFamily b) (derivativeCoefficientFamily g e c V) x := by
  simp only [covariantPolynomialDerivative, finitePolynomialFieldDerivative, polynomialConnectionAction,
    finitePolynomialField, Fintype.sum_sum_type, Fintype.sum_prod_type, derivativePolynomialFamily,
    derivativeCoefficientFamily, smul_eq_C_mul, map_sum, pderiv_C_mul, Finset.mul_sum, map_neg, map_mul]
  apply congrArg (fun z : MvPolynomial (I n) ℝ =>
    (∑ t, C ((fderiv ℝ c x (V x)) t) * b t) + z)
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro t _
  ring

lemma derivativeCoefficientFamily_smoothOn {Ω : Set (X n)} (hΩ : IsOpen Ω) {K : ℝ} {g : (MetricField n)}
    (h : Elliptic Ω K g) (hK : 0 < K) (e : (Frame n))
    (he : ∀ i, ContDiffOn ℝ ∞ (fun x => e x i) Ω) (c : (X n) → ι → ℝ) (V : (X n) → (X n))
    (hc : ContDiffOn ℝ ∞ c Ω) (hV : ContDiffOn ℝ ∞ V Ω) :
    ContDiffOn ℝ ∞ (derivativeCoefficientFamily g e c V) Ω := by
  apply contDiffOn_pi.mpr
  intro j
  cases j with
  | inl j => exact contDiffOn_pi.mp ((hc.fderiv_of_isOpen hΩ (by simp)).clm_apply hV) j
  | inr a =>
    exact (h.contDiffOn_frameConnection hΩ hK e he V hV a.1 a.2.1).neg.mul
      (contDiffOn_pi.mp hc a.2.2)

lemma derivativeCoefficientFamily_tsupport (g : (MetricField n)) (e : (Frame n))
    (c : (X n) → ι → ℝ) (V : (X n) → (X n)) :
    tsupport (derivativeCoefficientFamily g e c V) ⊆ tsupport c := by
  apply closure_minimal _ (isClosed_tsupport c)
  intro x hx
  by_contra hout
  have hc0 := image_eq_zero_of_notMem_tsupport hout
  have hdc0 := fderiv_of_notMem_tsupport (𝕜 := ℝ) hout
  apply hx
  funext j
  cases j with
  | inl j => simp [derivativeCoefficientFamily, hdc0]
  | inr a => simp [derivativeCoefficientFamily, hc0]

/-- Covariant derivatives of compactly supported coefficients are again globally smooth and
    supported in the same compact set, using only the local metric and frame assumptions. -/
lemma derivativeCoefficientFamily_smooth_compact {Ω : Set (X n)} (hΩ : IsOpen Ω) {K : ℝ} {g : (MetricField n)}
    (h : Elliptic Ω K g) (hK : 0 < K) (e : (Frame n))
    (he : ∀ i, ContDiffOn ℝ ∞ (fun x => e x i) Ω) (c : (X n) → ι → ℝ) (V : (X n) → (X n))
    (hc : ContDiff ℝ ∞ c) (hV : ContDiffOn ℝ ∞ V Ω)
    (hcompact : HasCompactSupport c) (hsupp : tsupport c ⊆ Ω) :
    ContDiff ℝ ∞ (derivativeCoefficientFamily g e c V) ∧
      HasCompactSupport (derivativeCoefficientFamily g e c V) ∧
      tsupport (derivativeCoefficientFamily g e c V) ⊆ tsupport c := by
  have ht := derivativeCoefficientFamily_tsupport g e c V
  exact ⟨contDiff_of_tsupport_subset hΩ _
    (derivativeCoefficientFamily_smoothOn hΩ h hK e he c V hc.contDiffOn hV) (ht.trans hsupp),
    hcompact.of_isClosed_subset (isClosed_tsupport _) ht, ht⟩

end CalderonN
