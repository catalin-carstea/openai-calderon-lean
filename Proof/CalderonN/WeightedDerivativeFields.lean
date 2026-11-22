module

public import Proof.CalderonN.PolynomialFamilies
public import Proof.CalderonN.WeightedPolynomial
import Mathlib.Tactic

@[expose] public section

/- Port of WeightedDerivativeFields.lean from the checked Proposition 5.3 release f308cb9d. -/
noncomputable section
open Set Filter MeasureTheory MvPolynomial
open scoped ContDiff Topology
namespace CalderonN
variable {n : ℕ}

variable [NeZero n]
open Set MvPolynomial

open OAI.AnisotropicCalderon.AngularPolynomial

variable {ι : Type*} [Fintype ι]

def weightedDerivativePolynomialFamily (b : ι → MvPolynomial (I n) ℝ) :
    (ι ⊕ ((I n) × (I n) × ι)) ⊕ ι → MvPolynomial (I n) ℝ := joinedPolynomialFamily (derivativePolynomialFamily b) b

def weightedDerivativeCoefficientFamily (g : (MetricField n)) (e : (Frame n)) (c : (X n) → ι → ℝ)
    (f : (X n) → ℝ) (k t : ℝ) (V : (X n) → (X n)) : (X n) → ((ι ⊕ ((I n) × (I n) × ι)) ⊕ ι) → ℝ :=
  joinedCoefficientFamily (fun x => t • derivativeCoefficientFamily g e c V x)
    (fun x => (k*fderiv ℝ f x (V x)) • c x)

lemma weightedPolynomialDerivative_eq_finite (g : (MetricField n)) (e : (Frame n))
    (b : ι → MvPolynomial (I n) ℝ) (c : (X n) → ι → ℝ) (f : (X n) → ℝ) (k t : ℝ) (V : (X n) → (X n)) (y : (X n)) :
    weightedPolynomialDerivative g e b c f k t y (V y) =
      finitePolynomialField (weightedDerivativePolynomialFamily b) (weightedDerivativeCoefficientFamily g e c f k t V) y := by
  rw [weightedDerivativePolynomialFamily, weightedDerivativeCoefficientFamily,
    finitePolynomialField_joined, finitePolynomialField_coeff_smul, finitePolynomialField_coeff_smul,
    ← covariantPolynomialDerivative_eq_augmented]
  simp only [weightedPolynomialDerivative, smul_eq_C_mul]

lemma weightedDerivativeCoefficientFamily_smoothOn {Ω : Set (X n)} (hΩ : IsOpen Ω) {K : ℝ}
    {g : (MetricField n)} (h : Elliptic Ω K g) (hK : 0 < K) (e : (Frame n))
    (he : ∀ i, ContDiffOn ℝ ∞ (fun x => e x i) Ω)
    (c : (X n) → ι → ℝ) (f : (X n) → ℝ) (k t : ℝ) (V : (X n) → (X n))
    (hc : ContDiffOn ℝ ∞ c Ω) (hf : ContDiffOn ℝ ∞ f Ω) (hV : ContDiffOn ℝ ∞ V Ω) :
    ContDiffOn ℝ ∞ (weightedDerivativeCoefficientFamily g e c f k t V) Ω := by
  apply contDiffOn_joinedCoefficientFamily
  · exact (contDiffOn_const : ContDiffOn ℝ ∞ (fun _ : (X n) => t) Ω).smul
      (derivativeCoefficientFamily_smoothOn hΩ h hK e he c V hc hV)
  · exact ((contDiffOn_const : ContDiffOn ℝ ∞ (fun _ : (X n) => k) Ω).mul
      ((hf.fderiv_of_isOpen hΩ (by simp)).clm_apply hV)).smul hc

lemma weightedDerivativeCoefficientFamily_tsupport (g : (MetricField n)) (e : (Frame n))
    (c : (X n) → ι → ℝ) (f : (X n) → ℝ) (k t : ℝ) (V : (X n) → (X n)) :
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

lemma weightedDerivativeCoefficientFamily_smooth_compact {Ω : Set (X n)} (hΩ : IsOpen Ω) {K : ℝ}
    {g : (MetricField n)} (h : Elliptic Ω K g) (hK : 0 < K) (e : (Frame n))
    (he : ∀ i, ContDiffOn ℝ ∞ (fun x => e x i) Ω)
    (c : (X n) → ι → ℝ) (f : (X n) → ℝ) (k t : ℝ) (V : (X n) → (X n))
    (hc : ContDiff ℝ ∞ c) (hf : ContDiffOn ℝ ∞ f Ω) (hV : ContDiffOn ℝ ∞ V Ω)
    (hcompact : HasCompactSupport c) (hsupp : tsupport c ⊆ Ω) :
    ContDiff ℝ ∞ (weightedDerivativeCoefficientFamily g e c f k t V) ∧
      HasCompactSupport (weightedDerivativeCoefficientFamily g e c f k t V) ∧
      tsupport (weightedDerivativeCoefficientFamily g e c f k t V) ⊆ tsupport c := by
  have ht := weightedDerivativeCoefficientFamily_tsupport g e c f k t V
  exact ⟨contDiff_of_tsupport_subset hΩ _
    (weightedDerivativeCoefficientFamily_smoothOn hΩ h hK e he c f k t V hc.contDiffOn hf hV) (ht.trans hsupp),
    hcompact.of_isClosed_subset (isClosed_tsupport _) ht, ht⟩

end CalderonN
