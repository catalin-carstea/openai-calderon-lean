import Proof.LegendreProjection

noncomputable section
set_option autoImplicit false
open Set MvPolynomial MeasureTheory
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.AngularPolynomial
open OAI.AnisotropicCalderon.SphereHarmonic

lemma sphereAverage_congr_frameVector (e : Frame) (y : X) (u v : X → ℂ)
    (h : ∀ w : UnitSphere, u (frameVector e y w.val) = v (frameVector e y w.val)) :
    sphereAverage e y u = sphereAverage e y v := by
  unfold sphereAverage
  apply integral_congr_ae
  filter_upwards [] with w
  exact h w

lemma fiberSq_congr_frameVector (e : Frame) (y : X) (u v : X → ℂ)
    (h : ∀ w : UnitSphere, u (frameVector e y w.val) = v (frameVector e y w.val)) :
    fiberSq e y u = fiberSq e y v := by
  unfold fiberSq
  congr 1
  apply sphereAverage_congr_frameVector
  intro w
  rw [h w]

lemma fiberSq_zero (e : Frame) (y : X) : fiberSq e y (fun _ => (0 : ℂ)) = 0 := by
  simp only [fiberSq, norm_zero, zero_pow (by decide : 2 ≠ 0), Complex.ofReal_zero]
  change (∫ w : UnitSphere, (0 : ℂ) ∂sphereProbability).re = 0
  simp

/-- The frozen Legendre kernel evaluated in the actual moving frame. -/
theorem degreePart_movingFramePolynomial_frameVector (g : MetricField) (e : Frame) (y : X)
    (hframe : ∀ i j, metricPair g y (e y i) (e y j) = if i = j then 1 else 0)
    (v : UnitSphere) (m k : ℕ) (p : MvPolynomial I ℝ) (hp : p.IsHomogeneous k) (hΔ : laplacian p = 0) :
    degreePart g e m y (fun w => (movingFramePolynomial g e p (y,w) : ℂ)) (frameVector e y v.val) =
      if m = k then ((eval (v.val : I → ℝ) p : ℝ) : ℂ) else 0 := by
  have hfun : (fun z : UnitSphere =>
      (legendre (metricPair g y (frameVector e y v.val) (frameVector e y z.val)) m : ℂ) *
      (movingFramePolynomial g e p (y,frameVector e y z.val) : ℂ)) =
      fun z : UnitSphere => ((legendre (∑ i, v.val i*z.val i) m * eval (z.val : I → ℝ) p : ℝ) : ℂ) := by
    funext z
    rw [metricPair_frameVector g e y v.val z.val hframe, movingFramePolynomial_frameVector g e y hframe]
    exact (Complex.ofReal_mul _ _).symm
  change (((2*(m : ℝ)+1) : ℝ) : ℂ) * (∫ z : UnitSphere,
      (legendre (metricPair g y (frameVector e y v.val) (frameVector e y z.val)) m : ℂ) *
        (movingFramePolynomial g e p (y,frameVector e y z.val) : ℂ) ∂sphereProbability) = _
  rw [hfun, integral_complex_ofReal]
  have hh := congrArg Complex.ofReal (sphere_legendre_projection v m k p hp hΔ)
  simpa only [Complex.ofReal_mul, apply_ite, Complex.ofReal_zero] using hh

theorem fiberSq_degreePart_movingFramePolynomial (g : MetricField) (e : Frame) (y : X)
    (hframe : ∀ i j, metricPair g y (e y i) (e y j) = if i = j then 1 else 0)
    (m k : ℕ) (p : MvPolynomial I ℝ) (hp : p.IsHomogeneous k) (hΔ : laplacian p = 0) :
    fiberSq e y (degreePart g e m y (fun w => (movingFramePolynomial g e p (y,w) : ℂ))) =
      if m = k then normalizedFischerSquare k p else 0 := by
  by_cases hmk : m = k
  · rw [if_pos hmk]
    calc
      _ = fiberSq e y (fun w => (movingFramePolynomial g e p (y,w) : ℂ)) := by
        apply fiberSq_congr_frameVector
        intro v
        rw [degreePart_movingFramePolynomial_frameVector g e y hframe v m k p hp hΔ, if_pos hmk,
          movingFramePolynomial_frameVector g e y hframe]
      _ = _ := fiberSq_movingFramePolynomial g e y hframe p hp hΔ
  · rw [if_neg hmk]
    calc
      _ = fiberSq e y (fun _ => (0 : ℂ)) := by
        apply fiberSq_congr_frameVector
        intro v
        rw [degreePart_movingFramePolynomial_frameVector g e y hframe v m k p hp hΔ, if_neg hmk]
      _ = _ := fiberSq_zero e y

/-- Exact Sobolev square for one harmonic degree using the frozen Legendre definition. -/
theorem sobolevSq_movingFramePolynomial (g : MetricField) (e : Frame) (y : X)
    (hframe : ∀ i j, metricPair g y (e y i) (e y j) = if i = j then 1 else 0)
    (s : ℝ) (k : ℕ) (p : MvPolynomial I ℝ) (hp : p.IsHomogeneous k) (hΔ : laplacian p = 0) :
    sobolevSq g e s y (fun w => (movingFramePolynomial g e p (y,w) : ℂ)) =
      (1+(k : ℝ))^(2*s) * normalizedFischerSquare k p := by
  unfold sobolevSq
  simp_rw [fiberSq_degreePart_movingFramePolynomial g e y hframe _ k p hp hΔ]
  rw [tsum_eq_single k]
  · rw [if_pos rfl]
  · intro m hm
    rw [if_neg hm, mul_zero]

variable {ι : Type*} [Fintype ι]

theorem sobolevSq_complexPolynomialField (g : MetricField) (e : Frame) (y : X)
    (hframe : ∀ i j, metricPair g y (e y i) (e y j) = if i = j then 1 else 0)
    (s : ℝ) (k : ℕ) (b : ι → MvPolynomial I ℝ) (hb : ∀ a, (b a).IsHomogeneous k)
    (hΔ : ∀ a, laplacian (b a) = 0) (c : X → ι → ℝ) :
    sobolevSq g e s y (fun w => complexPolynomialField g e b c (y,w)) =
      (1+(k : ℝ))^(2*s) * normalizedFischerSquare k (finitePolynomialField b c y) := by
  change sobolevSq g e s y (fun w => (movingFramePolynomial g e (finitePolynomialField b c y) (y,w) : ℂ)) = _
  exact sobolevSq_movingFramePolynomial g e y hframe s k _
    (finitePolynomialField_homogeneous b hb c y) (finitePolynomialField_harmonic b hΔ c y)

end ShrinkingSpheres
