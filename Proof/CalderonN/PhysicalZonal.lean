module

public import Proof.CalderonN.SphereRaisingEnergy
public import Proof.CalderonN.ComplexZonalProjection

import Mathlib.Tactic

@[expose] public section

noncomputable section
set_option autoImplicit false
open Set MvPolynomial MeasureTheory
namespace CalderonN
variable {n : ℕ} [NeZero n]
open OAI.AnisotropicCalderon.AngularPolynomial
open OAI.AnisotropicCalderon.SphereHarmonic

lemma sphereAverage_congr_frameVector (e : (Frame n)) (y : (X n)) (u v : (X n) → ℂ)
    (h : ∀ w : (UnitSphere n), u (frameVector e y w.val) = v (frameVector e y w.val)) :
    sphereAverage e y u = sphereAverage e y v := by
  unfold sphereAverage
  apply integral_congr_ae
  filter_upwards [] with w
  exact h w

lemma fiberSq_congr_frameVector (e : (Frame n)) (y : (X n)) (u v : (X n) → ℂ)
    (h : ∀ w : (UnitSphere n), u (frameVector e y w.val) = v (frameVector e y w.val)) :
    fiberSq e y u = fiberSq e y v := by
  unfold fiberSq
  congr 1
  apply sphereAverage_congr_frameVector
  intro w
  rw [h w]

lemma fiberSq_zero (e : (Frame n)) (y : (X n)) : fiberSq e y (fun _ => (0 : ℂ)) = 0 := by
  simp only [fiberSq, norm_zero, zero_pow (by decide : 2 ≠ 0), Complex.ofReal_zero]
  change (∫ w : (UnitSphere n), (0 : ℂ) ∂(unitSphereProbability n)).re = 0
  simp

/-- The exact sphere kernel selects the matching harmonic degree. -/
theorem sphere_zonal_projection_polynomial (hn : 3 ≤ n) (v : UnitSphere n)
    (m k : ℕ) (p : MvPolynomial (I n) ℝ) (hp : p.IsHomogeneous k) (hΔ : laplacian p = 0) :
    (harmonicMultiplicity n m : ℝ) * (∫ z : UnitSphere n,
      zonal n (∑ i, v.val i * z.val i) m * eval (z.val : I n → ℝ) p ∂unitSphereProbability n) =
      if m = k then eval (v.val : I n → ℝ) p else 0 := by
  have hAE := (polynomialSphere p).coeFn_toLp (p := 2) (𝕜 := ℝ) (unitSphereProbability n)
  have hIntegral := sphere_zonal_integral_eq_inner v m (polynomialSphereL2 p)
  have hEq : (∫ z : UnitSphere n, zonal n (∑ i, v.val i * z.val i) m *
      eval (z.val : I n → ℝ) p ∂unitSphereProbability n) =
      ∫ z : UnitSphere n, zonal n (∑ i, v.val i * z.val i) m * (polynomialSphereL2 p) z
        ∂unitSphereProbability n := by
    apply integral_congr_ae
    filter_upwards [hAE] with z hz
    exact congrArg (fun w => zonal n (∑ i, v.val i * z.val i) m * w) hz.symm
  rw [hEq, hIntegral]
  have hZ : zonalPolynomial (v.val : I n → ℝ) m ∈ harmonicHomogeneous n m :=
    ⟨zonalPolynomial_homogeneous _ m, zonalPolynomial_harmonic hn _ (unitSphere_sum_sq v) m⟩
  by_cases he : m = k
  · subst m
    rw [if_pos rfl, sphereFischerInner n k _ _ hZ ⟨hp,hΔ⟩]
    exact weighted_normalizedFischer_zonalPolynomial hn _ _ _ hp hΔ
  · rw [if_neg he, orthogonalSphereHarmonics n m k he _ (polynomialSphereL2_mem _ _ hZ)
      _ (polynomialSphereL2_mem _ _ ⟨hp,hΔ⟩), mul_zero]

theorem degreePart_movingFramePolynomial_frameVector (hn : 3 ≤ n) (g : MetricField n)
    (e : Frame n) (y : X n)
    (hframe : ∀ i j, metricPair g y (e y i) (e y j) = if i = j then 1 else 0)
    (v : UnitSphere n) (m k : ℕ) (p : MvPolynomial (I n) ℝ)
    (hp : p.IsHomogeneous k) (hΔ : laplacian p = 0) :
    degreePart g e m y (fun w => (movingFramePolynomial g e p (y,w) : ℂ)) (frameVector e y v.val) =
      if m = k then ((eval (v.val : I n → ℝ) p : ℝ) : ℂ) else 0 := by
  have hfun : (fun z : UnitSphere n =>
      (zonal n (metricPair g y (frameVector e y v.val) (frameVector e y z.val)) m : ℂ) *
      (movingFramePolynomial g e p (y,frameVector e y z.val) : ℂ)) =
      fun z : UnitSphere n => ((zonal n (∑ i, v.val i*z.val i) m *
        eval (z.val : I n → ℝ) p : ℝ) : ℂ) := by
    funext z
    rw [metricPair_frameVector g e y v.val z.val hframe,
      movingFramePolynomial_frameVector g e y hframe]
    exact (Complex.ofReal_mul _ _).symm
  change (harmonicMultiplicity n m : ℂ) * (∫ z : UnitSphere n,
      (zonal n (metricPair g y (frameVector e y v.val) (frameVector e y z.val)) m : ℂ) *
        (movingFramePolynomial g e p (y,frameVector e y z.val) : ℂ) ∂unitSphereProbability n) = _
  rw [hfun, integral_complex_ofReal]
  have hh := congrArg Complex.ofReal (sphere_zonal_projection_polynomial hn v m k p hp hΔ)
  simpa only [Complex.ofReal_mul, Complex.ofReal_natCast, apply_ite, Complex.ofReal_zero] using hh

theorem fiberSq_degreePart_movingFramePolynomial (hn : 3 ≤ n) (g : (MetricField n)) (e : (Frame n)) (y : (X n))
    (hframe : ∀ i j, metricPair g y (e y i) (e y j) = if i = j then 1 else 0)
    (m k : ℕ) (p : MvPolynomial (I n) ℝ) (hp : p.IsHomogeneous k) (hΔ : laplacian p = 0) :
    fiberSq e y (degreePart g e m y (fun w => (movingFramePolynomial g e p (y,w) : ℂ))) =
      if m = k then normalizedFischerSquare k p else 0 := by
  by_cases hmk : m = k
  · rw [if_pos hmk]
    calc
      _ = fiberSq e y (fun w => (movingFramePolynomial g e p (y,w) : ℂ)) := by
        apply fiberSq_congr_frameVector
        intro v
        rw [degreePart_movingFramePolynomial_frameVector hn g e y hframe v m k p hp hΔ, if_pos hmk,
          movingFramePolynomial_frameVector g e y hframe]
      _ = _ := fiberSq_movingFramePolynomial g e y hframe p hp hΔ
  · rw [if_neg hmk]
    calc
      _ = fiberSq e y (fun _ => (0 : ℂ)) := by
        apply fiberSq_congr_frameVector
        intro v
        rw [degreePart_movingFramePolynomial_frameVector hn g e y hframe v m k p hp hΔ, if_neg hmk]
      _ = _ := fiberSq_zero e y

/-- Exact Sobolev square for one harmonic degree using the protected sphere projector. -/
theorem sobolevSq_movingFramePolynomial (hn : 3 ≤ n) (g : (MetricField n)) (e : (Frame n)) (y : (X n))
    (hframe : ∀ i j, metricPair g y (e y i) (e y j) = if i = j then 1 else 0)
    (s : ℝ) (k : ℕ) (p : MvPolynomial (I n) ℝ) (hp : p.IsHomogeneous k) (hΔ : laplacian p = 0) :
    sobolevSq g e s y (fun w => (movingFramePolynomial g e p (y,w) : ℂ)) =
      (1+(k : ℝ))^(2*s) * normalizedFischerSquare k p := by
  unfold sobolevSq
  simp_rw [fiberSq_degreePart_movingFramePolynomial hn g e y hframe _ k p hp hΔ]
  rw [tsum_eq_single k]
  · rw [if_pos rfl]
  · intro m hm
    rw [if_neg hm, mul_zero]

variable {ι : Type*} [Fintype ι]

theorem sobolevSq_complexPolynomialField (hn : 3 ≤ n) (g : (MetricField n)) (e : (Frame n)) (y : (X n))
    (hframe : ∀ i j, metricPair g y (e y i) (e y j) = if i = j then 1 else 0)
    (s : ℝ) (k : ℕ) (b : ι → MvPolynomial (I n) ℝ) (hb : ∀ a, (b a).IsHomogeneous k)
    (hΔ : ∀ a, laplacian (b a) = 0) (c : (X n) → ι → ℝ) :
    sobolevSq g e s y (fun w => complexPolynomialField g e b c (y,w)) =
      (1+(k : ℝ))^(2*s) * normalizedFischerSquare k (finitePolynomialField b c y) := by
  change sobolevSq g e s y (fun w => (movingFramePolynomial g e (finitePolynomialField b c y) (y,w) : ℂ)) = _
  exact sobolevSq_movingFramePolynomial hn g e y hframe s k _
    (finitePolynomialField_homogeneous b hb c y) (finitePolynomialField_harmonic b hΔ c y)

end CalderonN
