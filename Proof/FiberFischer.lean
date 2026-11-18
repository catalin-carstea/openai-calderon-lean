import Proof.FiniteModeCoercivity
import Proof.Archive.LiteratureSphereFischerInner
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open Set MeasureTheory MvPolynomial
open scoped ContDiff
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.AngularPolynomial
open OAI.AnisotropicCalderon.SphereHarmonic

lemma sphereAverage_ofReal (e : Frame) (y : X) (u : X → ℝ) :
    sphereAverage e y (fun w => (u w : ℂ)) =
      (((∫ w : ↥standardSphere, u (frameVector e y w) ∂sphereProbability) : ℝ) : ℂ) := by
  change (∫ w : ↥standardSphere, (u (frameVector e y w) : ℂ) ∂sphereProbability) = _
  exact integral_complex_ofReal (μ := sphereProbability)
    (f := fun w : ↥standardSphere => u (frameVector e y w))

lemma fiberSq_ofReal (e : Frame) (y : X) (u : X → ℝ) :
    fiberSq e y (fun w => (u w : ℂ)) = ∫ w : ↥standardSphere, (u (frameVector e y w))^2 ∂sphereProbability := by
  simp only [fiberSq, Complex.norm_real, Real.norm_eq_abs, sq_abs]
  rw [sphereAverage_ofReal]
  rfl

lemma movingFramePolynomial_frameVector (g : MetricField) (e : Frame) (y : X)
    (hframe : ∀ i j, metricPair g y (e y i) (e y j) = if i = j then 1 else 0) (p : MvPolynomial I ℝ) (w : X) :
    movingFramePolynomial g e p (y, frameVector e y w) = eval (fun i => w i) p := by
  have hh (i : I) : movingFrameCoordinate g e i (y, frameVector e y w) = w i :=
    movingFrameCoordinate_frameVector g e y hframe (fun i => w i) i
  simp only [movingFramePolynomial, hh]

/-- The contract's complex fiber square agrees with the normalized Fischer square for a
    real harmonic homogeneous polynomial in the actual orthonormal frame. -/
theorem fiberSq_movingFramePolynomial (g : MetricField) (e : Frame) (y : X)
    (hframe : ∀ i j, metricPair g y (e y i) (e y j) = if i = j then 1 else 0)
    {k : ℕ} (p : MvPolynomial I ℝ) (hp : p.IsHomogeneous k) (hΔ : laplacian p = 0) :
    fiberSq e y (fun w => (movingFramePolynomial g e p (y,w) : ℂ)) = normalizedFischerSquare k p := by
  rw [fiberSq_ofReal]
  simp_rw [movingFramePolynomial_frameVector g e y hframe p]
  have hh := sphereFischerInner k p p ⟨hp,hΔ⟩ ⟨hp,hΔ⟩
  rw [polynomialSphereL2_inner] at hh
  simp only [pow_two]
  change (∫ w : UnitSphere, eval (w.val : Fin 3 → ℝ) p * eval (w.val : Fin 3 → ℝ) p ∂sphereProbability) = _
  exact hh

lemma horizontal_ofReal (g : MetricField) (F : X × X → ℝ) (y w a : X)
    (hF : DifferentiableAt ℝ F (y,w)) :
    horizontal g (fun z => (F z : ℂ)) y w a = ((horizontal (E := ℝ) g F y w a : ℝ) : ℂ) := by
  have hh := Complex.ofRealCLM.hasFDerivAt.comp (y,w) hF.hasFDerivAt
  change HasFDerivAt (fun z => (F z : ℂ)) _ (y,w) at hh
  rw [horizontal, hh.fderiv, ContinuousLinearMap.comp_apply]
  rfl

variable {ι : Type*} [Fintype ι]

def complexPolynomialField (g : MetricField) (e : Frame) (b : ι → MvPolynomial I ℝ) (c : X → ι → ℝ) : Field :=
  fun z => (evaluatedPolynomialField g e b c z : ℂ)

theorem complexPolynomialField_horizontal {Y : Set X} (hY : IsOpen Y) {K : ℝ} {g : MetricField}
    (h : Elliptic Y K g) (hK : 0 < K) (e : Frame)
    (he : ∀ i, ContDiffOn ℝ ∞ (fun x => e x i) Y)
    (hframe : ∀ y ∈ Y, ∀ i j, metricPair g y (e y i) (e y j) = if i = j then 1 else 0)
    (b : ι → MvPolynomial I ℝ) (c : X → ι → ℝ) (hc : ContDiffOn ℝ ∞ c Y)
    {y : X} (hy : y ∈ Y) (w a : X) :
    horizontal g (complexPolynomialField g e b c) y w a =
      (movingFramePolynomial g e (covariantPolynomialDerivative g e b c y a) (y,w) : ℂ) := by
  change horizontal g (fun z => (evaluatedPolynomialField g e b c z : ℂ)) y w a = _
  rw [horizontal_ofReal g _ y w a
    ((contDiffAt_evaluatedPolynomialField hY h e he b c hy (hc.contDiffAt (hY.mem_nhds hy)) w).differentiableAt (by simp)),
    evaluatedPolynomialField_horizontal hY h hK e he hframe b c hy
      ((hc.contDiffAt (hY.mem_nhds hy)).differentiableAt (by simp))]

theorem fiberSq_complexPolynomialField (g : MetricField) (e : Frame) (y : X)
    (hframe : ∀ i j, metricPair g y (e y i) (e y j) = if i = j then 1 else 0)
    {k : ℕ} (b : ι → MvPolynomial I ℝ) (hb : ∀ a, (b a).IsHomogeneous k)
    (hΔ : ∀ a, laplacian (b a) = 0) (c : X → ι → ℝ) :
    fiberSq e y (fun w => complexPolynomialField g e b c (y,w)) =
      normalizedFischerSquare k (finitePolynomialField b c y) := by
  change fiberSq e y (fun w => (movingFramePolynomial g e (finitePolynomialField b c y) (y,w) : ℂ)) = _
  exact fiberSq_movingFramePolynomial g e y hframe _ (finitePolynomialField_homogeneous b hb c y) (finitePolynomialField_harmonic b hΔ c y)

theorem fiberSq_complexPolynomialField_horizontal {Y : Set X} (hY : IsOpen Y) {K : ℝ} {g : MetricField}
    (h : Elliptic Y K g) (hK : 0 < K) (e : Frame)
    (he : ∀ i, ContDiffOn ℝ ∞ (fun x => e x i) Y)
    (hframe : ∀ y ∈ Y, ∀ i j, metricPair g y (e y i) (e y j) = if i = j then 1 else 0)
    {k : ℕ} (hk : 1 ≤ k) (b : ι → MvPolynomial I ℝ) (hb : ∀ a, (b a).IsHomogeneous k)
    (hΔ : ∀ a, laplacian (b a) = 0) (c : X → ι → ℝ) (hc : ContDiffOn ℝ ∞ c Y)
    {y : X} (hy : y ∈ Y) (i : I) :
    fiberSq e y (fun w => horizontal g (complexPolynomialField g e b c) y w (e y i)) =
      normalizedFischerSquare k (covariantPolynomialDerivative g e b c y (e y i)) := by
  have hfun : (fun w => horizontal g (complexPolynomialField g e b c) y w (e y i)) =
      fun w => (movingFramePolynomial g e (covariantPolynomialDerivative g e b c y (e y i)) (y,w) : ℂ) := by
    funext w
    exact complexPolynomialField_horizontal hY h hK e he hframe b c hc hy w (e y i)
  rw [hfun]
  exact fiberSq_movingFramePolynomial g e y (hframe y hy) _ (covariantPolynomialDerivative_homogeneous hk g e b hb c y (e y i))
    (covariantPolynomialDerivative_harmonic g e b hΔ c y (e y i) (frameConnection_skew hY h hK e he hframe hy (e y i)))

end ShrinkingSpheres
