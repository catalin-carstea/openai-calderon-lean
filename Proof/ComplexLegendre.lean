import Proof.ComplexPolynomial

noncomputable section
set_option autoImplicit false
open Set MeasureTheory MvPolynomial
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.AngularPolynomial
open OAI.AnisotropicCalderon.SphereHarmonic

lemma movingFrameComplexPolynomial_frameVector (g : MetricField) (e : Frame) (y : X)
    (hframe : ∀ i j, metricPair g y (e y i) (e y j) = if i = j then 1 else 0)
    (p q : MvPolynomial I ℝ) (v : X) :
    movingFrameComplexPolynomial g e p q (y,frameVector e y v) =
      Complex.mk (eval (v : I → ℝ) p) (eval (v : I → ℝ) q) := by
  simp only [movingFrameComplexPolynomial, movingFramePolynomial_frameVector g e y hframe]

lemma ofReal_mul_complexMk (a b c : ℝ) : (a : ℂ)*Complex.mk b c = Complex.mk (a*b) (a*c) := by
  apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im]

/-- The frozen Legendre kernel is the harmonic projection for both complex components. -/
theorem degreePart_movingFrameComplexPolynomial_frameVector (g : MetricField) (e : Frame) (y : X)
    (hframe : ∀ i j, metricPair g y (e y i) (e y j) = if i = j then 1 else 0)
    (v : UnitSphere) (m k : ℕ) (p q : MvPolynomial I ℝ)
    (hp : p.IsHomogeneous k) (hq : q.IsHomogeneous k) (hΔp : laplacian p = 0) (hΔq : laplacian q = 0) :
    degreePart g e m y (fun w => movingFrameComplexPolynomial g e p q (y,w)) (frameVector e y v.val) =
      if m = k then Complex.mk (eval (v.val : I → ℝ) p) (eval (v.val : I → ℝ) q) else 0 := by
  let Z := zonalPolynomial (v.val : I → ℝ) m
  have hfun : (fun z : UnitSphere =>
      (legendre (metricPair g y (frameVector e y v.val) (frameVector e y z.val)) m : ℂ) *
        movingFrameComplexPolynomial g e p q (y,frameVector e y z.val)) =
      fun z : UnitSphere => Complex.mk (eval (z.val : I → ℝ) (Z*p)) (eval (z.val : I → ℝ) (Z*q)) := by
    funext z
    rw [metricPair_frameVector g e y v.val z.val hframe, movingFrameComplexPolynomial_frameVector g e y hframe]
    simp only [Z, map_mul, eval_zonalPolynomial_unitSphere, ofReal_mul_complexMk]
  change (((2*(m : ℝ)+1) : ℝ) : ℂ) * (∫ z : UnitSphere,
      (legendre (metricPair g y (frameVector e y v.val) (frameVector e y z.val)) m : ℂ) *
        movingFrameComplexPolynomial g e p q (y,frameVector e y z.val) ∂sphereProbability) = _
  rw [hfun, integral_complexPolynomialSphere, ofReal_mul_complexMk]
  dsimp only [Z]
  simp_rw [map_mul, eval_zonalPolynomial_unitSphere]
  rw [sphere_legendre_projection v m k p hp hΔp, sphere_legendre_projection v m k q hq hΔq]
  by_cases hmk : m = k <;> simp [hmk]
  rfl

theorem fiberSq_degreePart_movingFrameComplexPolynomial (g : MetricField) (e : Frame) (y : X)
    (hframe : ∀ i j, metricPair g y (e y i) (e y j) = if i = j then 1 else 0)
    (m k : ℕ) (p q : MvPolynomial I ℝ)
    (hp : p.IsHomogeneous k) (hq : q.IsHomogeneous k) (hΔp : laplacian p = 0) (hΔq : laplacian q = 0) :
    fiberSq e y (degreePart g e m y (fun w => movingFrameComplexPolynomial g e p q (y,w))) =
      if m = k then normalizedFischerSquare k p + normalizedFischerSquare k q else 0 := by
  by_cases hmk : m = k
  · rw [if_pos hmk]
    calc
      _ = fiberSq e y (fun w => movingFrameComplexPolynomial g e p q (y,w)) := by
        apply fiberSq_congr_frameVector
        intro v
        rw [degreePart_movingFrameComplexPolynomial_frameVector g e y hframe v m k p q hp hq hΔp hΔq,
          if_pos hmk, movingFrameComplexPolynomial_frameVector g e y hframe]
      _ = _ := fiberSq_movingFrameComplexPolynomial g e y hframe p q hp hq hΔp hΔq
  · rw [if_neg hmk]
    calc
      _ = fiberSq e y (fun _ => (0 : ℂ)) := by
        apply fiberSq_congr_frameVector
        intro v
        rw [degreePart_movingFrameComplexPolynomial_frameVector g e y hframe v m k p q hp hq hΔp hΔq, if_neg hmk]
      _ = _ := fiberSq_zero e y

/-- Exact complex Sobolev square at one degree, using the frozen kernel and measure. -/
theorem sobolevSq_movingFrameComplexPolynomial (g : MetricField) (e : Frame) (y : X)
    (hframe : ∀ i j, metricPair g y (e y i) (e y j) = if i = j then 1 else 0)
    (s : ℝ) (k : ℕ) (p q : MvPolynomial I ℝ)
    (hp : p.IsHomogeneous k) (hq : q.IsHomogeneous k) (hΔp : laplacian p = 0) (hΔq : laplacian q = 0) :
    sobolevSq g e s y (fun w => movingFrameComplexPolynomial g e p q (y,w)) =
      (1+(k : ℝ))^(2*s) * (normalizedFischerSquare k p + normalizedFischerSquare k q) := by
  unfold sobolevSq
  simp_rw [fiberSq_degreePart_movingFrameComplexPolynomial g e y hframe _ k p q hp hq hΔp hΔq]
  rw [tsum_eq_single k]
  · rw [if_pos rfl]
  · intro m hm
    rw [if_neg hm, mul_zero]

end ShrinkingSpheres
