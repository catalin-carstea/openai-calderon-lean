module

public import Proof.CalderonN.CurvaturePolynomialFields
public import Proof.CalderonN.DensityDivergence
import Mathlib.Tactic

@[expose] public section

/- Port of IndexedPolynomialHessian.lean from the checked Proposition 5.3 release f308cb9d. -/
noncomputable section
open Set Filter MeasureTheory MvPolynomial
open scoped ContDiff Topology
namespace CalderonN
variable {n : ℕ}

variable [NeZero n]
open Set MvPolynomial

open OAI.AnisotropicCalderon.AngularPolynomial

def horizontalLinear {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (g : (MetricField n)) (F : (X n) × (X n) → E) (y w : (X n)) : (X n) →L[ℝ] E :=
  (fderiv ℝ F (y,w)).comp ((ContinuousLinearMap.id ℝ (X n)).prod (-(connectionBilinear g y).flip w))

lemma horizontalLinear_apply {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (g : (MetricField n)) (F : (X n) × (X n) → E) (y w a : (X n)) :
    horizontalLinear g F y w a = horizontal g F y w a := by
  simp [horizontalLinear, horizontal, connectionBilinear_apply]

lemma vectorFieldDeriv_horizontal {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (g : (MetricField n)) (V : (X n) → (X n)) (F : (X n) × (X n) → E) (y w : (X n)) :
    vectorFieldDeriv (horizontalVectorField (connectionBilinear g) V) F (y,w) =
      horizontal g F y w (V y) := by
  simp only [vectorFieldDeriv, horizontalVectorField, horizontal, connectionBilinear_apply]

lemma connection_symmetric {Ω : Set (X n)} (hΩ : IsOpen Ω) {K : ℝ} {g : (MetricField n)}
    (h : Elliptic Ω K g) {y : (X n)} (hy : y ∈ Ω) (a b : (X n)) : connection g y a b = connection g y b a := by
  ext k
  change (∑ i, ∑ j, christoffel g y k i j * a i * b j) =
    ∑ i, ∑ j, christoffel g y k i j * b i * a j
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [christoffel_lower_symmetric hΩ h hy k j i]
  ring

lemma covariantFrameVector_bracket {Ω : Set (X n)} (hΩ : IsOpen Ω) {K : ℝ} {g : (MetricField n)}
    (h : Elliptic Ω K g) (e : (Frame n)) {y : (X n)} (hy : y ∈ Ω) (i j : (I n)) :
    covariantFrameVector g e y (e y i) j - covariantFrameVector g e y (e y j) i =
      baseVectorFieldBracket (fun x => e x i) (fun x => e x j) y := by
  unfold covariantFrameVector baseVectorFieldBracket
  rw [connection_symmetric hΩ h hy (e y i) (e y j)]
  abel

variable {ι : Type*} [Fintype ι]

def indexedPolynomialHessian (g : (MetricField n)) (e : (Frame n))
    (b : ι → MvPolynomial (I n) ℝ) (c : (X n) → ι → ℝ) (y : (X n)) (i j : (I n)) : MvPolynomial (I n) ℝ :=
  covariantPolynomialDerivative g e (derivativePolynomialFamily b)
    (derivativeCoefficientFamily g e c (fun x => e x j)) y (e y i) -
    ∑ a, C (frameConnectionCoefficient g e y (e y i) j a) * covariantPolynomialDerivative g e b c y (e y a)

lemma covariantPolynomialDerivative_frameVector (g : (MetricField n)) (e : (Frame n))
    (b : ι → MvPolynomial (I n) ℝ) (c : (X n) → ι → ℝ) (y : (X n))
    (hframe : ∀ i j, metricPair g y (e y i) (e y j) = if i = j then 1 else 0) (i j : (I n)) :
    covariantPolynomialDerivative g e b c y (covariantFrameVector g e y (e y i) j) =
      ∑ a, C (frameConnectionCoefficient g e y (e y i) j a) * covariantPolynomialDerivative g e b c y (e y a) := by
  have hh := (frameBasis g e y hframe).sum_repr (covariantFrameVector g e y (e y i) j)
  conv_lhs => rw [← hh]
  simp only [frameBasis_apply, frameBasis_repr, ← covariantPolynomialLinear_apply,
    map_sum, map_smul, smul_eq_C_mul, frameConnectionCoefficient]

lemma indexedPolynomialHessian_evaluation {Ω : Set (X n)} (hΩ : IsOpen Ω) {K : ℝ} {g : (MetricField n)}
    (h : Elliptic Ω K g) (hK : 0 < K) (e : (Frame n))
    (he : ∀ i, ContDiffOn ℝ ∞ (fun x => e x i) Ω)
    (hframe : ∀ x ∈ Ω, ∀ i j, metricPair g x (e x i) (e x j) = if i = j then 1 else 0)
    (b : ι → MvPolynomial (I n) ℝ) (c : (X n) → ι → ℝ) (hc : ContDiffOn ℝ ∞ c Ω)
    {y : (X n)} (hy : y ∈ Ω) (w : (X n)) (i j : (I n)) :
    movingFramePolynomial g e (indexedPolynomialHessian g e b c y i j) (y,w) =
      vectorFieldDeriv (horizontalVectorField (connectionBilinear g) (fun x => e x i))
        (vectorFieldDeriv (horizontalVectorField (connectionBilinear g) (fun x => e x j))
          (evaluatedPolynomialField g e b c)) (y,w) -
      horizontal g (evaluatedPolynomialField g e b c) y w (covariantFrameVector g e y (e y i) j) := by
  have hdc := derivativeCoefficientFamily_smoothOn hΩ h hK e he c (fun x => e x j) hc (he j)
  have heq : vectorFieldDeriv (horizontalVectorField (connectionBilinear g) (fun x => e x j))
      (evaluatedPolynomialField g e b c) =ᶠ[nhds (y,w)]
      evaluatedPolynomialField g e (derivativePolynomialFamily b) (derivativeCoefficientFamily g e c (fun x => e x j)) := by
    filter_upwards [(hΩ.preimage continuous_fst).mem_nhds hy] with z hz
    rcases z with ⟨x,v⟩
    rw [vectorFieldDeriv_horizontal, evaluatedPolynomialField_horizontal hΩ h hK e he hframe b c hz
      ((hc.contDiffAt (hΩ.mem_nhds hz)).differentiableAt (by simp))]
    change movingFramePolynomial g e (covariantPolynomialDerivative g e b c x (e x j)) (x,v) = _
    rw [covariantPolynomialDerivative_eq_augmented g e b c (fun x => e x j) x]
    rfl
  have hmain := congrArg (fun L : (X n) × (X n) →L[ℝ] ℝ =>
    L (horizontalVectorField (connectionBilinear g) (fun x => e x i) (y,w))) heq.fderiv_eq
  change vectorFieldDeriv (horizontalVectorField (connectionBilinear g) (fun x => e x i))
      (vectorFieldDeriv (horizontalVectorField (connectionBilinear g) (fun x => e x j))
        (evaluatedPolynomialField g e b c)) (y,w) = _ at hmain
  change _ = vectorFieldDeriv (horizontalVectorField (connectionBilinear g) (fun x => e x i))
    (evaluatedPolynomialField g e (derivativePolynomialFamily b) (derivativeCoefficientFamily g e c (fun x => e x j))) (y,w) at hmain
  conv_rhs at hmain => rw [vectorFieldDeriv_horizontal]
  rw [evaluatedPolynomialField_horizontal hΩ h hK e he hframe _ _ hy
    ((hdc.contDiffAt (hΩ.mem_nhds hy)).differentiableAt (by simp))] at hmain
  rw [hmain, evaluatedPolynomialField_horizontal hΩ h hK e he hframe b c hy
    ((hc.contDiffAt (hΩ.mem_nhds hy)).differentiableAt (by simp)),
    covariantPolynomialDerivative_frameVector g e b c y (hframe y hy)]
  simp only [indexedPolynomialHessian, movingFramePolynomial, map_sub, map_sum, map_mul, eval_C]

/-- Covariant Hessian antisymmetry for the finite polynomial field, with the actual
    moving-frame lower-index correction. -/
theorem indexedPolynomialHessian_antisymm {Ω : Set (X n)} (hΩ : IsOpen Ω) {K : ℝ} {g : (MetricField n)}
    (h : Elliptic Ω K g) (hK : 0 < K) (e : (Frame n))
    (he : ∀ i, ContDiffOn ℝ ∞ (fun x => e x i) Ω)
    (hframe : ∀ x ∈ Ω, ∀ i j, metricPair g x (e x i) (e x j) = if i = j then 1 else 0)
    (b : ι → MvPolynomial (I n) ℝ) (c : (X n) → ι → ℝ) (hc : ContDiffOn ℝ ∞ c Ω)
    {y : (X n)} (hy : y ∈ Ω) (i j : (I n)) :
    indexedPolynomialHessian g e b c y i j - indexedPolynomialHessian g e b c y j i =
      curvaturePolynomialAction g e y (e y i) (e y j) (finitePolynomialField b c y) := by
  apply movingFramePolynomial_injective g e y (hframe y hy)
  intro w
  rw [movingFramePolynomial_sub]
  rw [indexedPolynomialHessian_evaluation hΩ h hK e he hframe b c hc hy,
    indexedPolynomialHessian_evaluation hΩ h hK e he hframe b c hc hy]
  have hh := metric_horizontal_commutator hΩ h hK (fun x => e x i) (fun x => e x j) (he i) (he j)
    (evaluatedPolynomialField g e b c) hy w
    (contDiffAt_evaluatedPolynomialField hΩ h e he b c hy (hc.contDiffAt (hΩ.mem_nhds hy)) w)
  rw [evaluatedPolynomialField_vertical_curvature hΩ h e he b c hy (hframe y hy)
    ((hc.contDiffAt (hΩ.mem_nhds hy)).differentiableAt (by simp))] at hh
  have hbr := vectorFieldDeriv_horizontal g
    (baseVectorFieldBracket (fun x => e x i) (fun x => e x j)) (evaluatedPolynomialField g e b c) y w
  rw [hbr] at hh
  have hcorr := congrArg (horizontalLinear g (evaluatedPolynomialField g e b c) y w)
    (covariantFrameVector_bracket hΩ h e hy i j)
  simp only [map_sub, horizontalLinear_apply] at hcorr
  linarith only [hh, hcorr]

end CalderonN
