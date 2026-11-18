import Proof.SphereRaisingEnergy
import Proof.Archive.LiteratureOrthogonalSphereHarmonics
import Proof.Archive.LiteratureDenseSphereHarmonics

noncomputable section
set_option autoImplicit false
open Set MeasureTheory MvPolynomial
open scoped ContDiff InnerProductSpace
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.AngularPolynomial
open OAI.AnisotropicCalderon.SphereHarmonic

lemma sphereAverage_movingFramePolynomial (g : MetricField) (e : Frame) (y : X)
    (hframe : ∀ i j, metricPair g y (e y i) (e y j) = if i = j then 1 else 0)
    (p : MvPolynomial I ℝ) :
    sphereAverage e y (fun w => (movingFramePolynomial g e p (y,w) : ℂ)) =
      ((⟪polynomialSphereL2 p, polynomialSphereL2 1⟫_ℝ : ℝ) : ℂ) := by
  rw [sphereAverage_ofReal]
  congr 1
  simp_rw [movingFramePolynomial_frameVector g e y hframe p]
  rw [polynomialSphereL2_inner]
  simp only [map_one, mul_one]
  rfl

lemma sphereAverage_movingFramePolynomial_eq_zero (g : MetricField) (e : Frame) (y : X)
    (hframe : ∀ i j, metricPair g y (e y i) (e y j) = if i = j then 1 else 0)
    {k : ℕ} (hk : 1 ≤ k) (p : MvPolynomial I ℝ) (hp : p.IsHomogeneous k) (hΔ : laplacian p = 0) :
    sphereAverage e y (fun w => (movingFramePolynomial g e p (y,w) : ℂ)) = 0 := by
  have h1 : (1 : MvPolynomial I ℝ) ∈ harmonicHomogeneous 0 :=
    ⟨isHomogeneous_one I ℝ, by simp [laplacian]⟩
  have hh := orthogonalSphereHarmonics k 0 (by omega) _
    (polynomialSphereL2_mem k p ⟨hp,hΔ⟩) _ (polynomialSphereL2_mem 0 1 h1)
  rw [sphereAverage_movingFramePolynomial g e y hframe p, hh]
  rfl

variable {ι : Type*} [Fintype ι]

lemma smoothNear_complexPolynomialField {Y : Set X} (hY : IsOpen Y) {K : ℝ} {g : MetricField}
    (h : Elliptic Y K g) (e : Frame) (he : ∀ i, ContDiffOn ℝ ∞ (fun x => e x i) Y)
    (b : ι → MvPolynomial I ℝ) (c : X → ι → ℝ) (hc : ContDiffOn ℝ ∞ c Y) :
    smoothNear (complexPolynomialField g e b c) (bundle Y g) := by
  refine ⟨Prod.fst ⁻¹' Y, hY.preimage continuous_fst, fun z hz => hz.1, ?_⟩
  intro z hz
  have hh := contDiffAt_evaluatedPolynomialField hY h e he b c hz
    (hc.contDiffAt (hY.mem_nhds hz)) z.2
  exact (Complex.ofRealCLM.contDiff.contDiffAt.comp z hh).contDiffWithinAt

/-- Real finite harmonic fields of positive degree are genuine mean-zero tests for the
    frozen geometric contract, with no special construction of the radius. -/
theorem test_complexPolynomialField {Y : Set X} (hY : IsOpen Y) {K : ℝ} {g : MetricField}
    (h : Elliptic Y K g) (e : Frame) (he : ∀ i, ContDiffOn ℝ ∞ (fun x => e x i) Y)
    (hframe : ∀ y ∈ Y, ∀ i j, metricPair g y (e y i) (e y j) = if i = j then 1 else 0)
    {k : ℕ} (hk : 1 ≤ k) (b : ι → MvPolynomial I ℝ) (hb : ∀ a, (b a).IsHomogeneous k)
    (hΔ : ∀ a, laplacian (b a) = 0) (c : X → ι → ℝ) (hc : ContDiffOn ℝ ∞ c Y)
    (hcompact : HasCompactSupport c) (hsupp : tsupport c ⊆ Y) :
    Test Y g e (complexPolynomialField g e b c) := by
  refine ⟨smoothNear_complexPolynomialField hY h e he b c hc, ⟨tsupport c, hcompact, hsupp, ?_⟩, ?_⟩
  · intro y hy w hw
    simp [complexPolynomialField, evaluatedPolynomialField,
      finitePolynomialField_zero_outside b c hy.2, movingFramePolynomial]
  · intro y hy
    exact sphereAverage_movingFramePolynomial_eq_zero g e y (hframe y hy) hk _
      (finitePolynomialField_homogeneous b hb c y) (finitePolynomialField_harmonic b hΔ c y)

/-- Physical fiber Pythagoras for finitely many distinct harmonic degrees. -/
theorem fiberSq_movingFramePolynomial_sum (g : MetricField) (e : Frame) (y : X)
    (hframe : ∀ i j, metricPair g y (e y i) (e y j) = if i = j then 1 else 0)
    (s : Finset ℕ) (p : ℕ → MvPolynomial I ℝ)
    (hp : ∀ k ∈ s, (p k).IsHomogeneous k) (hΔ : ∀ k ∈ s, laplacian (p k) = 0) :
    fiberSq e y (fun w => ((movingFramePolynomial g e (∑ k ∈ s, p k) (y,w) : ℝ) : ℂ)) =
      ∑ k ∈ s, normalizedFischerSquare k (p k) := by
  rw [fiberSq_ofReal]
  simp_rw [movingFramePolynomial_frameVector g e y hframe]
  have hh := polynomialSphereL2_finite_pythagoras sphereFischerInner orthogonalSphereHarmonics s p
    (fun k hk => ⟨hp k hk,hΔ k hk⟩)
  rw [← map_sum, ← real_inner_self_eq_norm_sq, polynomialSphereL2_inner] at hh
  simp only [pow_two]
  change (∫ w : UnitSphere, eval (w.val : Fin 3 → ℝ) (∑ k ∈ s, p k) *
    eval (w.val : Fin 3 → ℝ) (∑ k ∈ s, p k) ∂sphereProbability) = _
  exact hh

end ShrinkingSpheres
