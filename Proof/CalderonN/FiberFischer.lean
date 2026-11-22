module

public import Proof.CalderonN.FiniteModeCoercivity
public import Proof.CalderonN.ComplexZonalProjection
public import Proof.CalderonN.GaussianSphere
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Tactic

@[expose] public section

/- Port of FiberFischer.lean from the checked Proposition 5.3 release f308cb9d. -/
noncomputable section
open Set Filter MeasureTheory MvPolynomial
open scoped ContDiff Topology
namespace CalderonN
variable {n : ℕ}

variable [NeZero n]

open OAI.AnisotropicCalderon.AngularPolynomial
open OAI.AnisotropicCalderon.SphereHarmonic

lemma sphereAverage_ofReal (e : (Frame n)) (y : (X n)) (u : (X n) → ℝ) :
    sphereAverage e y (fun w => (u w : ℂ)) =
      (((∫ w : UnitSphere n, u (frameVector e y w) ∂(sphereProbability n)) : ℝ) : ℂ) := by
  change (∫ w : UnitSphere n, (u (frameVector e y w) : ℂ) ∂(sphereProbability n)) = _
  exact integral_complex_ofReal (μ := (sphereProbability n))
    (f := fun w : UnitSphere n => u (frameVector e y w))

lemma fiberSq_ofReal (e : (Frame n)) (y : (X n)) (u : (X n) → ℝ) :
    fiberSq e y (fun w => (u w : ℂ)) = ∫ w : UnitSphere n, (u (frameVector e y w))^2 ∂(sphereProbability n) := by
  rw [fiberSq_eq_integral_norm_sq]
  simp only [Complex.norm_real, Real.norm_eq_abs, sq_abs, unitSphereProbability] <;> rfl


lemma movingFramePolynomial_frameVector (g : (MetricField n)) (e : (Frame n)) (y : (X n))
    (hframe : ∀ i j, metricPair g y (e y i) (e y j) = if i = j then 1 else 0) (p : MvPolynomial (I n) ℝ) (w : (X n)) :
    movingFramePolynomial g e p (y, frameVector e y w) = eval (fun i => w i) p := by
  have hh (i : (I n)) : movingFrameCoordinate g e i (y, frameVector e y w) = w i :=
    movingFrameCoordinate_frameVector g e y hframe (fun i => w i) i
  simp only [movingFramePolynomial, hh]

/-- The contract's complex fiber square agrees with the normalized Fischer square for a
    real harmonic homogeneous polynomial in the actual orthonormal frame. -/
theorem fiberSq_movingFramePolynomial (g : (MetricField n)) (e : (Frame n)) (y : (X n))
    (hframe : ∀ i j, metricPair g y (e y i) (e y j) = if i = j then 1 else 0)
    {k : ℕ} (p : MvPolynomial (I n) ℝ) (hp : p.IsHomogeneous k) (hΔ : laplacian p = 0) :
    fiberSq e y (fun w => (movingFramePolynomial g e p (y,w) : ℂ)) = normalizedFischerSquare k p := by
  rw [fiberSq_ofReal]
  simp_rw [movingFramePolynomial_frameVector g e y hframe p]
  have hh := sphereFischerInner n k p p ⟨hp,hΔ⟩ ⟨hp,hΔ⟩
  rw [polynomialSphereL2_inner] at hh
  simp only [pow_two]
  change (∫ w : UnitSphere n, eval (w.val : Fin n → ℝ) p * eval (w.val : Fin n → ℝ) p ∂(sphereProbability n)) = _
  exact hh

lemma horizontal_ofReal (g : (MetricField n)) (F : (X n) × (X n) → ℝ) (y w a : (X n))
    (hF : DifferentiableAt ℝ F (y,w)) :
    horizontal g (fun z => (F z : ℂ)) y w a = ((horizontal (E := ℝ) g F y w a : ℝ) : ℂ) := by
  have hh := Complex.ofRealCLM.hasFDerivAt.comp (y,w) hF.hasFDerivAt
  change HasFDerivAt (fun z => (F z : ℂ)) _ (y,w) at hh
  rw [horizontal, hh.fderiv, ContinuousLinearMap.comp_apply]
  rfl

variable {ι : Type*} [Fintype ι]

def complexPolynomialField (g : (MetricField n)) (e : (Frame n)) (b : ι → MvPolynomial (I n) ℝ) (c : (X n) → ι → ℝ) : (Field n) :=
  fun z => (evaluatedPolynomialField g e b c z : ℂ)

theorem complexPolynomialField_horizontal {Y : Set (X n)} (hY : IsOpen Y) {K : ℝ} {g : (MetricField n)}
    (h : Elliptic Y K g) (hK : 0 < K) (e : (Frame n))
    (he : ∀ i, ContDiffOn ℝ ∞ (fun x => e x i) Y)
    (hframe : ∀ y ∈ Y, ∀ i j, metricPair g y (e y i) (e y j) = if i = j then 1 else 0)
    (b : ι → MvPolynomial (I n) ℝ) (c : (X n) → ι → ℝ) (hc : ContDiffOn ℝ ∞ c Y)
    {y : (X n)} (hy : y ∈ Y) (w a : (X n)) :
    horizontal g (complexPolynomialField g e b c) y w a =
      (movingFramePolynomial g e (covariantPolynomialDerivative g e b c y a) (y,w) : ℂ) := by
  change horizontal g (fun z => (evaluatedPolynomialField g e b c z : ℂ)) y w a = _
  rw [horizontal_ofReal g _ y w a
    ((contDiffAt_evaluatedPolynomialField hY h e he b c hy (hc.contDiffAt (hY.mem_nhds hy)) w).differentiableAt (by simp)),
    evaluatedPolynomialField_horizontal hY h hK e he hframe b c hy
      ((hc.contDiffAt (hY.mem_nhds hy)).differentiableAt (by simp))]

theorem fiberSq_complexPolynomialField (g : (MetricField n)) (e : (Frame n)) (y : (X n))
    (hframe : ∀ i j, metricPair g y (e y i) (e y j) = if i = j then 1 else 0)
    {k : ℕ} (b : ι → MvPolynomial (I n) ℝ) (hb : ∀ a, (b a).IsHomogeneous k)
    (hΔ : ∀ a, laplacian (b a) = 0) (c : (X n) → ι → ℝ) :
    fiberSq e y (fun w => complexPolynomialField g e b c (y,w)) =
      normalizedFischerSquare k (finitePolynomialField b c y) := by
  change fiberSq e y (fun w => (movingFramePolynomial g e (finitePolynomialField b c y) (y,w) : ℂ)) = _
  exact fiberSq_movingFramePolynomial g e y hframe _ (finitePolynomialField_homogeneous b hb c y) (finitePolynomialField_harmonic b hΔ c y)

theorem fiberSq_complexPolynomialField_horizontal {Y : Set (X n)} (hY : IsOpen Y) {K : ℝ} {g : (MetricField n)}
    (h : Elliptic Y K g) (hK : 0 < K) (e : (Frame n))
    (he : ∀ i, ContDiffOn ℝ ∞ (fun x => e x i) Y)
    (hframe : ∀ y ∈ Y, ∀ i j, metricPair g y (e y i) (e y j) = if i = j then 1 else 0)
    {k : ℕ} (hk : 1 ≤ k) (b : ι → MvPolynomial (I n) ℝ) (hb : ∀ a, (b a).IsHomogeneous k)
    (hΔ : ∀ a, laplacian (b a) = 0) (c : (X n) → ι → ℝ) (hc : ContDiffOn ℝ ∞ c Y)
    {y : (X n)} (hy : y ∈ Y) (i : (I n)) :
    fiberSq e y (fun w => horizontal g (complexPolynomialField g e b c) y w (e y i)) =
      normalizedFischerSquare k (covariantPolynomialDerivative g e b c y (e y i)) := by
  have hfun : (fun w => horizontal g (complexPolynomialField g e b c) y w (e y i)) =
      fun w => (movingFramePolynomial g e (covariantPolynomialDerivative g e b c y (e y i)) (y,w) : ℂ) := by
    funext w
    exact complexPolynomialField_horizontal hY h hK e he hframe b c hc hy w (e y i)
  rw [hfun]
  exact fiberSq_movingFramePolynomial g e y (hframe y hy) _ (covariantPolynomialDerivative_homogeneous hk g e b hb c y (e y i))
    (covariantPolynomialDerivative_harmonic g e b hΔ c y (e y i) (frameConnection_skew hY h hK e he hframe hy (e y i)))

end CalderonN
