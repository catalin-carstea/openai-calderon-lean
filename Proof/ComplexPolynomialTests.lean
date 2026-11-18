import Proof.UniformComplexCoercivity

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open Set MeasureTheory MvPolynomial
open scoped ContDiff
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.AngularPolynomial
open OAI.AnisotropicCalderon.SphereHarmonic

lemma sphereAverage_movingFrameComplexPolynomial (g : MetricField) (e : Frame) (y : X)
    (hframe : ∀ i j, metricPair g y (e y i) (e y j) = if i = j then 1 else 0) (p q : MvPolynomial I ℝ) :
    sphereAverage e y (fun w => movingFrameComplexPolynomial g e p q (y,w)) =
      Complex.mk (sphereAverage e y (fun w => (movingFramePolynomial g e p (y,w) : ℂ))).re
        (sphereAverage e y (fun w => (movingFramePolynomial g e q (y,w) : ℂ))).re := by
  change (∫ w : UnitSphere, movingFrameComplexPolynomial g e p q (y,frameVector e y w.val) ∂sphereProbability) = _
  simp_rw [movingFrameComplexPolynomial_frameVector g e y hframe]
  rw [integral_complexPolynomialSphere, sphereAverage_ofReal, sphereAverage_ofReal]
  simp_rw [movingFramePolynomial_frameVector g e y hframe]
  rfl

lemma sphereAverage_movingFrameComplexPolynomial_eq_zero (g : MetricField) (e : Frame) (y : X)
    (hframe : ∀ i j, metricPair g y (e y i) (e y j) = if i = j then 1 else 0)
    {k : ℕ} (hk : 1 ≤ k) (p q : MvPolynomial I ℝ) (hp : p.IsHomogeneous k) (hq : q.IsHomogeneous k)
    (hΔp : laplacian p = 0) (hΔq : laplacian q = 0) :
    sphereAverage e y (fun w => movingFrameComplexPolynomial g e p q (y,w)) = 0 := by
  rw [sphereAverage_movingFrameComplexPolynomial g e y hframe p q,
    sphereAverage_movingFramePolynomial_eq_zero g e y hframe hk p hp hΔp,
    sphereAverage_movingFramePolynomial_eq_zero g e y hframe hk q hq hΔq]
  rfl

variable {ι : Type*} [Fintype ι]

lemma smoothNear_pairedPolynomialField {Y : Set X} (hY : IsOpen Y) {K : ℝ} {g : MetricField}
    (h : Elliptic Y K g) (e : Frame) (he : ∀ i, ContDiffOn ℝ ∞ (fun x => e x i) Y)
    (b : ι → MvPolynomial I ℝ) (c d : X → ι → ℝ) (hc : ContDiffOn ℝ ∞ c Y) (hd : ContDiffOn ℝ ∞ d Y) :
    smoothNear (pairedPolynomialField g e b c d) (bundle Y g) := by
  refine ⟨Prod.fst ⁻¹' Y, hY.preimage continuous_fst, fun z hz => hz.1, ?_⟩
  intro z hz
  have hC := contDiffAt_evaluatedPolynomialField hY h e he b c hz (hc.contDiffAt (hY.mem_nhds hz)) z.2
  have hD := contDiffAt_evaluatedPolynomialField hY h e he b d hz (hd.contDiffAt (hY.mem_nhds hz)) z.2
  exact (Complex.equivRealProdCLM.symm.contDiff.contDiffAt.comp z (hC.prodMk hD)).contDiffWithinAt

/-- Compact complex finite harmonic fields of positive degree satisfy the frozen test
    conditions, with the same sphere mean and a common compact support. -/
theorem test_pairedPolynomialField {Y : Set X} (hY : IsOpen Y) {K : ℝ} {g : MetricField}
    (h : Elliptic Y K g) (e : Frame) (he : ∀ i, ContDiffOn ℝ ∞ (fun x => e x i) Y)
    (hframe : ∀ y ∈ Y, ∀ i j, metricPair g y (e y i) (e y j) = if i = j then 1 else 0)
    {k : ℕ} (hk : 1 ≤ k) (b : ι → MvPolynomial I ℝ) (hb : ∀ a, (b a).IsHomogeneous k)
    (hΔ : ∀ a, laplacian (b a) = 0) (c d : X → ι → ℝ) (hc : ContDiffOn ℝ ∞ c Y) (hd : ContDiffOn ℝ ∞ d Y)
    (hcompactc : HasCompactSupport c) (hcompactd : HasCompactSupport d) (hsuppc : tsupport c ⊆ Y) (hsuppd : tsupport d ⊆ Y) :
    Test Y g e (pairedPolynomialField g e b c d) := by
  refine ⟨smoothNear_pairedPolynomialField hY h e he b c d hc hd,
    ⟨tsupport c ∪ tsupport d, hcompactc.union hcompactd, union_subset hsuppc hsuppd, ?_⟩, ?_⟩
  · intro y hy w hw
    have hc0 := finitePolynomialField_zero_outside b c (fun ht => hy.2 (Or.inl ht))
    have hd0 := finitePolynomialField_zero_outside b d (fun ht => hy.2 (Or.inr ht))
    simp only [pairedPolynomialField, hc0, hd0, movingFrameComplexPolynomial, movingFramePolynomial, map_zero]
    rfl
  · intro y hy
    change sphereAverage e y (fun w => movingFrameComplexPolynomial g e
      (finitePolynomialField b c y) (finitePolynomialField b d y) (y,w)) = 0
    exact sphereAverage_movingFrameComplexPolynomial_eq_zero g e y (hframe y hy) hk _ _
      (finitePolynomialField_homogeneous b hb c y) (finitePolynomialField_homogeneous b hb d y)
      (finitePolynomialField_harmonic b hΔ c y) (finitePolynomialField_harmonic b hΔ d y)

end ShrinkingSpheres
