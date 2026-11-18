import Proof.MetricSmooth
import Proof.Localization

set_option maxSynthPendingDepth 10
noncomputable section
open Set MvPolynomial
open scoped ContDiff
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.AngularPolynomial

variable {ι : Type*} [Fintype ι]

/-- Fixed polynomial family containing a field and the finitely many polynomial connection
    terms in its derivative. -/
def derivativePolynomialFamily (b : ι → MvPolynomial I ℝ) : ι ⊕ (I × I × ι) → MvPolynomial I ℝ
  | .inl j => b j
  | .inr a => MvPolynomial.X a.1 * pderiv a.2.1 (b a.2.2)

def derivativeCoefficientFamily (g : MetricField) (e : Frame) (c : X → ι → ℝ) (V : X → X)
    (x : X) : ι ⊕ (I × I × ι) → ℝ
  | .inl j => fderiv ℝ c x (V x) j
  | .inr a => -frameConnectionCoefficient g e x (V x) a.1 a.2.1 * c x a.2.2

lemma covariantPolynomialDerivative_eq_augmented (g : MetricField) (e : Frame)
    (b : ι → MvPolynomial I ℝ) (c : X → ι → ℝ) (V : X → X) (x : X) :
    covariantPolynomialDerivative g e b c x (V x) =
      finitePolynomialField (derivativePolynomialFamily b) (derivativeCoefficientFamily g e c V) x := by
  simp only [covariantPolynomialDerivative, finitePolynomialFieldDerivative, polynomialConnectionAction,
    finitePolynomialField, Fintype.sum_sum_type, Fintype.sum_prod_type, derivativePolynomialFamily,
    derivativeCoefficientFamily, smul_eq_C_mul, map_sum, pderiv_C_mul, Finset.mul_sum, map_neg, map_mul]
  apply congrArg (fun z : MvPolynomial I ℝ =>
    (∑ t, C ((fderiv ℝ c x (V x)) t) * b t) + z)
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro t _
  ring

lemma derivativeCoefficientFamily_smoothOn {Ω : Set X} (hΩ : IsOpen Ω) {K : ℝ} {g : MetricField}
    (h : Elliptic Ω K g) (hK : 0 < K) (e : Frame)
    (he : ∀ i, ContDiffOn ℝ ∞ (fun x => e x i) Ω) (c : X → ι → ℝ) (V : X → X)
    (hc : ContDiffOn ℝ ∞ c Ω) (hV : ContDiffOn ℝ ∞ V Ω) :
    ContDiffOn ℝ ∞ (derivativeCoefficientFamily g e c V) Ω := by
  apply contDiffOn_pi.mpr
  intro j
  cases j with
  | inl j => exact contDiffOn_pi.mp ((hc.fderiv_of_isOpen hΩ (by simp)).clm_apply hV) j
  | inr a =>
    exact (h.contDiffOn_frameConnection hΩ hK e he V hV a.1 a.2.1).neg.mul
      (contDiffOn_pi.mp hc a.2.2)

lemma derivativeCoefficientFamily_tsupport (g : MetricField) (e : Frame)
    (c : X → ι → ℝ) (V : X → X) :
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
lemma derivativeCoefficientFamily_smooth_compact {Ω : Set X} (hΩ : IsOpen Ω) {K : ℝ} {g : MetricField}
    (h : Elliptic Ω K g) (hK : 0 < K) (e : Frame)
    (he : ∀ i, ContDiffOn ℝ ∞ (fun x => e x i) Ω) (c : X → ι → ℝ) (V : X → X)
    (hc : ContDiff ℝ ∞ c) (hV : ContDiffOn ℝ ∞ V Ω)
    (hcompact : HasCompactSupport c) (hsupp : tsupport c ⊆ Ω) :
    ContDiff ℝ ∞ (derivativeCoefficientFamily g e c V) ∧
      HasCompactSupport (derivativeCoefficientFamily g e c V) ∧
      tsupport (derivativeCoefficientFamily g e c V) ⊆ tsupport c := by
  have ht := derivativeCoefficientFamily_tsupport g e c V
  exact ⟨contDiff_of_tsupport_subset hΩ _
    (derivativeCoefficientFamily_smoothOn hΩ h hK e he c V hc.contDiffOn hV) (ht.trans hsupp),
    hcompact.of_isClosed_subset (isClosed_tsupport _) ht, ht⟩

end ShrinkingSpheres
