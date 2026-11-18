import Proof.PhysicalModeCoercivity

noncomputable section
set_option autoImplicit false
open Set MvPolynomial MeasureTheory
open scoped InnerProductSpace
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.AngularPolynomial
open OAI.AnisotropicCalderon.SphereHarmonic

lemma sphere_legendre_integral_eq_inner (w : UnitSphere) (m : ℕ) (p : MvPolynomial I ℝ) :
    (∫ z : UnitSphere, legendre (∑ i, w.val i*z.val i) m * eval (z.val : I → ℝ) p ∂sphereProbability) =
      ⟪polynomialSphereL2 (zonalPolynomial (w.val : I → ℝ) m), polynomialSphereL2 p⟫_ℝ := by
  rw [polynomialSphereL2_inner]
  simp_rw [eval_zonalPolynomial_unitSphere]

lemma sphere_legendre_inner_projection (w : UnitSphere) (m k : ℕ) (p : MvPolynomial I ℝ)
    (hp : p.IsHomogeneous k) (hΔ : laplacian p = 0) :
    (2*(m : ℝ)+1) * ⟪polynomialSphereL2 (zonalPolynomial (w.val : I → ℝ) m), polynomialSphereL2 p⟫_ℝ =
      if m = k then eval (w.val : I → ℝ) p else 0 := by
  rw [← sphere_legendre_integral_eq_inner]
  exact sphere_legendre_projection w m k p hp hΔ

lemma sphere_legendre_inner_sum_projection (w : UnitSphere) (m : ℕ) (s : Finset ℕ)
    (p : ℕ → MvPolynomial I ℝ) (hp : ∀ k ∈ s, (p k).IsHomogeneous k) (hΔ : ∀ k ∈ s, laplacian (p k) = 0) :
    (2*(m : ℝ)+1) * ⟪polynomialSphereL2 (zonalPolynomial (w.val : I → ℝ) m), polynomialSphereL2 (∑ k ∈ s, p k)⟫_ℝ =
      if m ∈ s then eval (w.val : I → ℝ) (p m) else 0 := by
  rw [map_sum, inner_sum, Finset.mul_sum]
  have hh : (∑ k ∈ s, (2*(m : ℝ)+1) * ⟪polynomialSphereL2 (zonalPolynomial (w.val : I → ℝ) m), polynomialSphereL2 (p k)⟫_ℝ) =
      ∑ k ∈ s, if m = k then eval (w.val : I → ℝ) (p k) else 0 := by
    apply Finset.sum_congr rfl
    intro k hk
    exact sphere_legendre_inner_projection w m k (p k) (hp k hk) (hΔ k hk)
  rw [hh]
  simp

lemma degreePart_movingFramePolynomial_frameVector_inner (g : MetricField) (e : Frame) (y : X)
    (hframe : ∀ i j, metricPair g y (e y i) (e y j) = if i = j then 1 else 0)
    (v : UnitSphere) (m : ℕ) (p : MvPolynomial I ℝ) :
    degreePart g e m y (fun w => (movingFramePolynomial g e p (y,w) : ℂ)) (frameVector e y v.val) =
      (((2*(m : ℝ)+1) * ⟪polynomialSphereL2 (zonalPolynomial (v.val : I → ℝ) m), polynomialSphereL2 p⟫_ℝ : ℝ) : ℂ) := by
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
  rw [hfun, integral_complex_ofReal, sphere_legendre_integral_eq_inner, Complex.ofReal_mul]

/-- Exact frozen degree projections of a finite sum, in the actual moving frame. -/
theorem degreePart_movingFramePolynomial_sum (g : MetricField) (e : Frame) (y : X)
    (hframe : ∀ i j, metricPair g y (e y i) (e y j) = if i = j then 1 else 0)
    (v : UnitSphere) (m : ℕ) (s : Finset ℕ) (p : ℕ → MvPolynomial I ℝ)
    (hp : ∀ k ∈ s, (p k).IsHomogeneous k) (hΔ : ∀ k ∈ s, laplacian (p k) = 0) :
    degreePart g e m y (fun w => (movingFramePolynomial g e (∑ k ∈ s, p k) (y,w) : ℂ)) (frameVector e y v.val) =
      if m ∈ s then ((eval (v.val : I → ℝ) (p m) : ℝ) : ℂ) else 0 := by
  rw [degreePart_movingFramePolynomial_frameVector_inner g e y hframe v m,
    sphere_legendre_inner_sum_projection v m s p hp hΔ]
  by_cases hm : m ∈ s <;> simp [hm]

theorem fiberSq_degreePart_movingFramePolynomial_sum (g : MetricField) (e : Frame) (y : X)
    (hframe : ∀ i j, metricPair g y (e y i) (e y j) = if i = j then 1 else 0)
    (m : ℕ) (s : Finset ℕ) (p : ℕ → MvPolynomial I ℝ)
    (hp : ∀ k ∈ s, (p k).IsHomogeneous k) (hΔ : ∀ k ∈ s, laplacian (p k) = 0) :
    fiberSq e y (degreePart g e m y (fun w => (movingFramePolynomial g e (∑ k ∈ s, p k) (y,w) : ℂ))) =
      if m ∈ s then normalizedFischerSquare m (p m) else 0 := by
  by_cases hm : m ∈ s
  · rw [if_pos hm]
    calc
      _ = fiberSq e y (fun w => (movingFramePolynomial g e (p m) (y,w) : ℂ)) := by
        apply fiberSq_congr_frameVector
        intro v
        rw [degreePart_movingFramePolynomial_sum g e y hframe v m s p hp hΔ, if_pos hm,
          movingFramePolynomial_frameVector g e y hframe]
      _ = _ := fiberSq_movingFramePolynomial g e y hframe _ (hp m hm) (hΔ m hm)
  · rw [if_neg hm]
    calc
      _ = fiberSq e y (fun _ => (0 : ℂ)) := by
        apply fiberSq_congr_frameVector
        intro v
        rw [degreePart_movingFramePolynomial_sum g e y hframe v m s p hp hΔ, if_neg hm]
      _ = _ := fiberSq_zero e y

/-- Sobolev Pythagoras for any finite family of harmonic degrees, with the frozen kernel. -/
theorem sobolevSq_movingFramePolynomial_sum (g : MetricField) (e : Frame) (y : X)
    (hframe : ∀ i j, metricPair g y (e y i) (e y j) = if i = j then 1 else 0)
    (a : ℝ) (s : Finset ℕ) (p : ℕ → MvPolynomial I ℝ)
    (hp : ∀ k ∈ s, (p k).IsHomogeneous k) (hΔ : ∀ k ∈ s, laplacian (p k) = 0) :
    sobolevSq g e a y (fun w => (movingFramePolynomial g e (∑ k ∈ s, p k) (y,w) : ℂ)) =
      ∑ k ∈ s, (1+(k : ℝ))^(2*a) * normalizedFischerSquare k (p k) := by
  unfold sobolevSq
  simp_rw [fiberSq_degreePart_movingFramePolynomial_sum g e y hframe _ s p hp hΔ]
  rw [tsum_eq_sum (s:=s)]
  · apply Finset.sum_congr rfl
    intro k hk
    rw [if_pos hk]
  · intro k hk
    rw [if_neg hk, mul_zero]

end ShrinkingSpheres
