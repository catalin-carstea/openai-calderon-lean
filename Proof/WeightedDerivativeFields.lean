import Proof.PolynomialFamilies
import Proof.WeightedPolynomial

noncomputable section
open Set MvPolynomial
open scoped ContDiff
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.AngularPolynomial

variable {ι : Type*} [Fintype ι]

def weightedDerivativePolynomialFamily (b : ι → MvPolynomial I ℝ) :
    (ι ⊕ (I × I × ι)) ⊕ ι → MvPolynomial I ℝ := joinedPolynomialFamily (derivativePolynomialFamily b) b

def weightedDerivativeCoefficientFamily (g : MetricField) (e : Frame) (c : X → ι → ℝ)
    (f : X → ℝ) (k t : ℝ) (V : X → X) : X → ((ι ⊕ (I × I × ι)) ⊕ ι) → ℝ :=
  joinedCoefficientFamily (fun x => t • derivativeCoefficientFamily g e c V x)
    (fun x => (k*fderiv ℝ f x (V x)) • c x)

lemma weightedPolynomialDerivative_eq_finite (g : MetricField) (e : Frame)
    (b : ι → MvPolynomial I ℝ) (c : X → ι → ℝ) (f : X → ℝ) (k t : ℝ) (V : X → X) (y : X) :
    weightedPolynomialDerivative g e b c f k t y (V y) =
      finitePolynomialField (weightedDerivativePolynomialFamily b) (weightedDerivativeCoefficientFamily g e c f k t V) y := by
  rw [weightedDerivativePolynomialFamily, weightedDerivativeCoefficientFamily,
    finitePolynomialField_joined, finitePolynomialField_coeff_smul, finitePolynomialField_coeff_smul,
    ← covariantPolynomialDerivative_eq_augmented]
  simp only [weightedPolynomialDerivative, smul_eq_C_mul]

lemma weightedDerivativeCoefficientFamily_smoothOn {Ω : Set X} (hΩ : IsOpen Ω) {K : ℝ}
    {g : MetricField} (h : Elliptic Ω K g) (hK : 0 < K) (e : Frame)
    (he : ∀ i, ContDiffOn ℝ ∞ (fun x => e x i) Ω)
    (c : X → ι → ℝ) (f : X → ℝ) (k t : ℝ) (V : X → X)
    (hc : ContDiffOn ℝ ∞ c Ω) (hf : ContDiffOn ℝ ∞ f Ω) (hV : ContDiffOn ℝ ∞ V Ω) :
    ContDiffOn ℝ ∞ (weightedDerivativeCoefficientFamily g e c f k t V) Ω := by
  apply contDiffOn_joinedCoefficientFamily
  · exact (contDiffOn_const : ContDiffOn ℝ ∞ (fun _ : X => t) Ω).smul
      (derivativeCoefficientFamily_smoothOn hΩ h hK e he c V hc hV)
  · exact ((contDiffOn_const : ContDiffOn ℝ ∞ (fun _ : X => k) Ω).mul
      ((hf.fderiv_of_isOpen hΩ (by simp)).clm_apply hV)).smul hc

lemma weightedDerivativeCoefficientFamily_tsupport (g : MetricField) (e : Frame)
    (c : X → ι → ℝ) (f : X → ℝ) (k t : ℝ) (V : X → X) :
    tsupport (weightedDerivativeCoefficientFamily g e c f k t V) ⊆ tsupport c := by
  apply closure_minimal _ (isClosed_tsupport c)
  intro x hx
  by_contra hout
  have hc0 := image_eq_zero_of_notMem_tsupport hout
  have hd0 := fderiv_of_notMem_tsupport (𝕜 := ℝ) hout
  apply hx
  funext a
  rcases a with a | a
  · rcases a with a | ⟨i,j,a⟩ <;>
      simp [weightedDerivativeCoefficientFamily, joinedCoefficientFamily, derivativeCoefficientFamily, hc0, hd0]
  · simp [weightedDerivativeCoefficientFamily, joinedCoefficientFamily, hc0]

lemma weightedDerivativeCoefficientFamily_smooth_compact {Ω : Set X} (hΩ : IsOpen Ω) {K : ℝ}
    {g : MetricField} (h : Elliptic Ω K g) (hK : 0 < K) (e : Frame)
    (he : ∀ i, ContDiffOn ℝ ∞ (fun x => e x i) Ω)
    (c : X → ι → ℝ) (f : X → ℝ) (k t : ℝ) (V : X → X)
    (hc : ContDiff ℝ ∞ c) (hf : ContDiffOn ℝ ∞ f Ω) (hV : ContDiffOn ℝ ∞ V Ω)
    (hcompact : HasCompactSupport c) (hsupp : tsupport c ⊆ Ω) :
    ContDiff ℝ ∞ (weightedDerivativeCoefficientFamily g e c f k t V) ∧
      HasCompactSupport (weightedDerivativeCoefficientFamily g e c f k t V) ∧
      tsupport (weightedDerivativeCoefficientFamily g e c f k t V) ⊆ tsupport c := by
  have ht := weightedDerivativeCoefficientFamily_tsupport g e c f k t V
  exact ⟨contDiff_of_tsupport_subset hΩ _
    (weightedDerivativeCoefficientFamily_smoothOn hΩ h hK e he c f k t V hc.contDiffOn hf hV) (ht.trans hsupp),
    hcompact.of_isClosed_subset (isClosed_tsupport _) ht, ht⟩

end ShrinkingSpheres
