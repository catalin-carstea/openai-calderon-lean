import Proof.CovectorTransport

noncomputable section
open Set MeasureTheory MvPolynomial
open scoped ContDiff
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.AngularPolynomial

lemma integrable_local_supported {J : Type*} [Fintype J] {Ω : Set X} (hΩ : IsOpen Ω)
    (c : X → J → ℝ) (hcompact : HasCompactSupport c) (hsupp : tsupport c ⊆ Ω)
    (u : X → ℝ) (hu : ContDiffOn ℝ ∞ u Ω) (hzero : ∀ x ∉ tsupport c, u x = 0) : Integrable u := by
  have ht : tsupport u ⊆ tsupport c := by
    apply closure_minimal _ (isClosed_tsupport c)
    intro x hx
    by_contra hout
    exact hx (hzero x hout)
  exact (contDiff_of_tsupport_subset hΩ u hu (ht.trans hsupp)).continuous.integrable_of_hasCompactSupport
    (hcompact.of_isClosed_subset (isClosed_tsupport _) ht)

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

lemma finitePolynomialField_zero_outside (b : ι → MvPolynomial I ℝ) (c : X → ι → ℝ)
    {y : X} (hy : y ∉ tsupport c) : finitePolynomialField b c y = 0 := by
  simp [finitePolynomialField, image_eq_zero_of_notMem_tsupport hy]

lemma covariantPolynomialDerivative_zero_outside (g : MetricField) (e : Frame)
    (b : ι → MvPolynomial I ℝ) (c : X → ι → ℝ) {y : X} (hy : y ∉ tsupport c) (a : X) :
    covariantPolynomialDerivative g e b c y a = 0 := by
  simp [covariantPolynomialDerivative, finitePolynomialFieldDerivative, finitePolynomialField,
    polynomialConnectionAction, image_eq_zero_of_notMem_tsupport hy, fderiv_of_notMem_tsupport (𝕜 := ℝ) hy]

lemma covectorPolynomialDerivative_zero_outside (g : MetricField) (e : Frame)
    (b : ι → I → MvPolynomial I ℝ) (c : X → ι → ℝ) {y : X} (hy : y ∉ tsupport c) (a : X) (i : I) :
    covectorPolynomialDerivative g e b c y a i = 0 := by
  simp [covectorPolynomialDerivative, covariantPolynomialDerivative_zero_outside g e _ c hy,
    finitePolynomialField_zero_outside _ c hy]

lemma contDiffOn_covariant_fischer_left {Ω : Set X} (hΩ : IsOpen Ω) {K : ℝ}
    {g : MetricField} (h : Elliptic Ω K g) (hK : 0 < K) (e : Frame)
    (he : ∀ i, ContDiffOn ℝ ∞ (fun x => e x i) Ω) (V : X → X) (hV : ContDiffOn ℝ ∞ V Ω)
    (b : ι → MvPolynomial I ℝ) (d : κ → MvPolynomial I ℝ) (c : X → ι → ℝ) (z : X → κ → ℝ)
    (hc : ContDiffOn ℝ ∞ c Ω) (hz : ContDiffOn ℝ ∞ z Ω) :
    ContDiffOn ℝ ∞ (fun x => fischerInner (covariantPolynomialDerivative g e b c x (V x))
      (finitePolynomialField d z x)) Ω := by
  have hh := contDiffOn_fischerPair (derivativePolynomialFamily b) d (derivativeCoefficientFamily g e c V) z
    (derivativeCoefficientFamily_smoothOn hΩ h hK e he c V hc hV) hz
  simpa only [← covariantPolynomialDerivative_eq_augmented] using hh

lemma contDiffOn_covariant_fischer_right {Ω : Set X} (hΩ : IsOpen Ω) {K : ℝ}
    {g : MetricField} (h : Elliptic Ω K g) (hK : 0 < K) (e : Frame)
    (he : ∀ i, ContDiffOn ℝ ∞ (fun x => e x i) Ω) (V : X → X) (hV : ContDiffOn ℝ ∞ V Ω)
    (b : ι → MvPolynomial I ℝ) (d : κ → MvPolynomial I ℝ) (c : X → ι → ℝ) (z : X → κ → ℝ)
    (hc : ContDiffOn ℝ ∞ c Ω) (hz : ContDiffOn ℝ ∞ z Ω) :
    ContDiffOn ℝ ∞ (fun x => fischerInner (finitePolynomialField b c x)
      (covariantPolynomialDerivative g e d z x (V x))) Ω := by
  simpa only [fischerInner_symm] using contDiffOn_covariant_fischer_left hΩ h hK e he V hV d b z c hz hc

lemma contDiffOn_covector_fischer_left {Ω : Set X} (hΩ : IsOpen Ω) {K : ℝ}
    {g : MetricField} (h : Elliptic Ω K g) (hK : 0 < K) (e : Frame)
    (he : ∀ i, ContDiffOn ℝ ∞ (fun x => e x i) Ω) (V : X → X) (hV : ContDiffOn ℝ ∞ V Ω)
    (b : ι → I → MvPolynomial I ℝ) (d : κ → MvPolynomial I ℝ) (c : X → ι → ℝ) (z : X → κ → ℝ)
    (hc : ContDiffOn ℝ ∞ c Ω) (hz : ContDiffOn ℝ ∞ z Ω) (i : I) :
    ContDiffOn ℝ ∞ (fun x => fischerInner (covectorPolynomialDerivative g e b c x (V x) i)
      (finitePolynomialField d z x)) Ω := by
  simp only [covectorPolynomialDerivative, fischerInner_sub_left, fischerInner_sum_left, fischerInner_C_mul_left]
  exact (contDiffOn_covariant_fischer_left hΩ h hK e he V hV _ d c z hc hz).sub
    (ContDiffOn.sum (fun j _ => (h.contDiffOn_frameConnection hΩ hK e he V hV i j).mul
      (contDiffOn_fischerPair (fun t => b t j) d c z hc hz)))

lemma contDiffOn_covector_fischer_right {Ω : Set X} (hΩ : IsOpen Ω) {K : ℝ}
    {g : MetricField} (h : Elliptic Ω K g) (hK : 0 < K) (e : Frame)
    (he : ∀ i, ContDiffOn ℝ ∞ (fun x => e x i) Ω) (V : X → X) (hV : ContDiffOn ℝ ∞ V Ω)
    (b : ι → MvPolynomial I ℝ) (d : κ → I → MvPolynomial I ℝ) (c : X → ι → ℝ) (z : X → κ → ℝ)
    (hc : ContDiffOn ℝ ∞ c Ω) (hz : ContDiffOn ℝ ∞ z Ω) (i : I) :
    ContDiffOn ℝ ∞ (fun x => fischerInner (finitePolynomialField b c x)
      (covectorPolynomialDerivative g e d z x (V x) i)) Ω := by
  simpa only [fischerInner_symm] using contDiffOn_covector_fischer_left hΩ h hK e he V hV d b z c hz hc i

lemma integrable_covariant_fischer_left {Ω : Set X} (hΩ : IsOpen Ω) {K : ℝ}
    {g : MetricField} (h : Elliptic Ω K g) (hK : 0 < K) (e : Frame)
    (he : ∀ i, ContDiffOn ℝ ∞ (fun x => e x i) Ω) (V : X → X) (hV : ContDiffOn ℝ ∞ V Ω)
    (ρ : X → ℝ) (hρ : ContDiffOn ℝ ∞ ρ Ω)
    (b : ι → MvPolynomial I ℝ) (d : κ → MvPolynomial I ℝ) (c : X → ι → ℝ) (z : X → κ → ℝ)
    (hc : ContDiffOn ℝ ∞ c Ω) (hz : ContDiffOn ℝ ∞ z Ω)
    (hcompact : HasCompactSupport c) (hsupp : tsupport c ⊆ Ω) :
    Integrable (fun x => ρ x * fischerInner (covariantPolynomialDerivative g e b c x (V x))
      (finitePolynomialField d z x)) := by
  apply integrable_local_supported hΩ c hcompact hsupp _
    (hρ.mul (contDiffOn_covariant_fischer_left hΩ h hK e he V hV b d c z hc hz))
  intro x hx
  simp [covariantPolynomialDerivative_zero_outside g e b c hx, fischerInner_zero_left]

lemma integrable_covariant_fischer_right {Ω : Set X} (hΩ : IsOpen Ω) {K : ℝ}
    {g : MetricField} (h : Elliptic Ω K g) (hK : 0 < K) (e : Frame)
    (he : ∀ i, ContDiffOn ℝ ∞ (fun x => e x i) Ω) (V : X → X) (hV : ContDiffOn ℝ ∞ V Ω)
    (ρ : X → ℝ) (hρ : ContDiffOn ℝ ∞ ρ Ω)
    (b : ι → MvPolynomial I ℝ) (d : κ → MvPolynomial I ℝ) (c : X → ι → ℝ) (z : X → κ → ℝ)
    (hc : ContDiffOn ℝ ∞ c Ω) (hz : ContDiffOn ℝ ∞ z Ω)
    (hcompact : HasCompactSupport c) (hsupp : tsupport c ⊆ Ω) :
    Integrable (fun x => ρ x * fischerInner (finitePolynomialField b c x)
      (covariantPolynomialDerivative g e d z x (V x))) := by
  apply integrable_local_supported hΩ c hcompact hsupp _
    (hρ.mul (contDiffOn_covariant_fischer_right hΩ h hK e he V hV b d c z hc hz))
  intro x hx
  simp [finitePolynomialField_zero_outside b c hx, fischerInner_zero_left]

end ShrinkingSpheres
