module

public import Proof.CalderonN.ComplexPolynomial

import Mathlib.Tactic

@[expose] public section

noncomputable section
set_option autoImplicit false
open Set MeasureTheory MvPolynomial
namespace CalderonN
variable {n : ℕ} [NeZero n]
open OAI.AnisotropicCalderon.AngularPolynomial
open OAI.AnisotropicCalderon.SphereHarmonic

lemma movingFrameComplexPolynomial_frameVector (g : (MetricField n)) (e : (Frame n)) (y : (X n))
    (hframe : ∀ i j, metricPair g y (e y i) (e y j) = if i = j then 1 else 0)
    (p q : MvPolynomial (I n) ℝ) (v : (X n)) :
    movingFrameComplexPolynomial g e p q (y,frameVector e y v) =
      Complex.mk (eval (v : (I n) → ℝ) p) (eval (v : (I n) → ℝ) q) := by
  simp only [movingFrameComplexPolynomial, movingFramePolynomial_frameVector g e y hframe]

lemma ofReal_mul_complexMk (a b c : ℝ) : (a : ℂ)*Complex.mk b c = Complex.mk (a*b) (a*c) := by
  apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im]

/-- The protected zonal kernel is the harmonic projection for both complex components. -/
theorem degreePart_movingFrameComplexPolynomial_frameVector (hn : 3 ≤ n) (g : (MetricField n)) (e : (Frame n)) (y : (X n))
    (hframe : ∀ i j, metricPair g y (e y i) (e y j) = if i = j then 1 else 0)
    (v : (UnitSphere n)) (m k : ℕ) (p q : MvPolynomial (I n) ℝ)
    (hp : p.IsHomogeneous k) (hq : q.IsHomogeneous k) (hΔp : laplacian p = 0) (hΔq : laplacian q = 0) :
    degreePart g e m y (fun w => movingFrameComplexPolynomial g e p q (y,w)) (frameVector e y v.val) =
      if m = k then Complex.mk (eval (v.val : (I n) → ℝ) p) (eval (v.val : (I n) → ℝ) q) else 0 := by
  let F := fun w => movingFrameComplexPolynomial g e p q (y,w)
  have hfun : (fun z : UnitSphere n =>
      (zonal n (metricPair g y (frameVector e y v.val) (frameVector e y z.val)) m : ℂ) *
        F (frameVector e y z.val)) =
      fun z : UnitSphere n => Complex.mk
        (zonal n (∑ i,v.val i*z.val i) m * eval (z.val : I n → ℝ) p)
        (zonal n (∑ i,v.val i*z.val i) m * eval (z.val : I n → ℝ) q) := by
    funext z
    rw [metricPair_frameVector g e y v.val z.val hframe]
    dsimp only [F]
    rw [movingFrameComplexPolynomial_frameVector g e y hframe, ofReal_mul_complexMk]
  have hInt (a : MvPolynomial (I n) ℝ) : Integrable (fun z : UnitSphere n =>
      zonal n (∑ i, v.val i*z.val i) m * eval (z.val : I n → ℝ) a)
      (unitSphereProbability n) := by
    apply (integrable_zonal_mul_Lp v m (polynomialSphereL2 a)).congr
    filter_upwards [(polynomialSphere a).coeFn_toLp (p := 2) (𝕜 := ℝ) (unitSphereProbability n)]
      with z hz
    exact congrArg (fun w => zonal n (∑ i, v.val i*z.val i) m * w) hz
  change (harmonicMultiplicity n m : ℂ) * (∫ z : UnitSphere n,
      (zonal n (metricPair g y (frameVector e y v.val) (frameVector e y z.val)) m : ℂ) *
      F (frameVector e y z.val) ∂unitSphereProbability n) = _
  rw [hfun, integral_complexMk_of_integrable (hInt p) (hInt q), ← Complex.ofReal_natCast,
    ofReal_mul_complexMk, sphere_zonal_projection_polynomial hn v m k p hp hΔp,
    sphere_zonal_projection_polynomial hn v m k q hq hΔq]
  by_cases he : m = k <;> simp [he]
  rfl

theorem fiberSq_degreePart_movingFrameComplexPolynomial (hn : 3 ≤ n) (g : (MetricField n)) (e : (Frame n)) (y : (X n))
    (hframe : ∀ i j, metricPair g y (e y i) (e y j) = if i = j then 1 else 0)
    (m k : ℕ) (p q : MvPolynomial (I n) ℝ)
    (hp : p.IsHomogeneous k) (hq : q.IsHomogeneous k) (hΔp : laplacian p = 0) (hΔq : laplacian q = 0) :
    fiberSq e y (degreePart g e m y (fun w => movingFrameComplexPolynomial g e p q (y,w))) =
      if m = k then normalizedFischerSquare k p + normalizedFischerSquare k q else 0 := by
  by_cases hmk : m = k
  · rw [if_pos hmk]
    calc
      _ = fiberSq e y (fun w => movingFrameComplexPolynomial g e p q (y,w)) := by
        apply fiberSq_congr_frameVector
        intro v
        rw [degreePart_movingFrameComplexPolynomial_frameVector hn g e y hframe v m k p q hp hq hΔp hΔq,
          if_pos hmk, movingFrameComplexPolynomial_frameVector g e y hframe]
      _ = _ := fiberSq_movingFrameComplexPolynomial g e y hframe p q hp hq hΔp hΔq
  · rw [if_neg hmk]
    calc
      _ = fiberSq e y (fun _ => (0 : ℂ)) := by
        apply fiberSq_congr_frameVector
        intro v
        rw [degreePart_movingFrameComplexPolynomial_frameVector hn g e y hframe v m k p q hp hq hΔp hΔq, if_neg hmk]
      _ = _ := fiberSq_zero e y

/-- Exact complex Sobolev square at one degree, using the frozen kernel and measure. -/
theorem sobolevSq_movingFrameComplexPolynomial (hn : 3 ≤ n) (g : (MetricField n)) (e : (Frame n)) (y : (X n))
    (hframe : ∀ i j, metricPair g y (e y i) (e y j) = if i = j then 1 else 0)
    (s : ℝ) (k : ℕ) (p q : MvPolynomial (I n) ℝ)
    (hp : p.IsHomogeneous k) (hq : q.IsHomogeneous k) (hΔp : laplacian p = 0) (hΔq : laplacian q = 0) :
    sobolevSq g e s y (fun w => movingFrameComplexPolynomial g e p q (y,w)) =
      (1+(k : ℝ))^(2*s) * (normalizedFischerSquare k p + normalizedFischerSquare k q) := by
  unfold sobolevSq
  simp_rw [fiberSq_degreePart_movingFrameComplexPolynomial hn g e y hframe _ k p q hp hq hΔp hΔq]
  rw [tsum_eq_single k]
  · rw [if_pos rfl]
  · intro m hm
    rw [if_neg hm, mul_zero]

end CalderonN
