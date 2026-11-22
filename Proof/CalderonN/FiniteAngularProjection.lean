module

public import Proof.CalderonN.FiniteAngularPythagoras

import Mathlib.Tactic

@[expose] public section

noncomputable section
set_option autoImplicit false
open Set MeasureTheory MvPolynomial
open scoped InnerProductSpace
namespace CalderonN
variable {N : ℕ} [NeZero N]
open OAI.AnisotropicCalderon.AngularPolynomial
open OAI.AnisotropicCalderon.SphereHarmonic

private theorem sphere_zonal_integral_eq_polynomial_inner (v : UnitSphere N)
    (m : ℕ) (p : MvPolynomial (I N) ℝ) :
    (∫ z : UnitSphere N, zonal N (∑ i, v.val i * z.val i) m *
      eval (z.val : I N → ℝ) p ∂unitSphereProbability N) =
      ⟪polynomialSphereL2 (zonalPolynomial (v.val : I N → ℝ) m), polynomialSphereL2 p⟫_ℝ := by
  refine (integral_congr_ae ?_).trans (sphere_zonal_integral_eq_inner v m (polynomialSphereL2 p))
  filter_upwards [(polynomialSphere p).coeFn_toLp (p := 2) (𝕜 := ℝ) (unitSphereProbability N)]
    with z hz
  exact congrArg (fun w => zonal N (∑ i, v.val i * z.val i) m * w) hz.symm

lemma degreePart_movingFrameComplexPolynomial_frameVector_inner (g : (MetricField N)) (e : (Frame N)) (y : (X N))
    (hframe : ∀ i j, metricPair g y (e y i) (e y j) = if i = j then 1 else 0)
    (v : (UnitSphere N)) (m : ℕ) (p q : MvPolynomial (I N) ℝ) :
    degreePart g e m y (fun w => movingFrameComplexPolynomial g e p q (y,w)) (frameVector e y v.val) =
      Complex.mk ((harmonicMultiplicity N m : ℝ)*⟪polynomialSphereL2 (zonalPolynomial (v.val : (I N) → ℝ) m),polynomialSphereL2 p⟫_ℝ)
        ((harmonicMultiplicity N m : ℝ)*⟪polynomialSphereL2 (zonalPolynomial (v.val : (I N) → ℝ) m),polynomialSphereL2 q⟫_ℝ) := by
  let Z := zonalPolynomial (v.val : (I N) → ℝ) m
  have hfun : (fun z : (UnitSphere N) =>
      (zonal N (metricPair g y (frameVector e y v.val) (frameVector e y z.val)) m : ℂ) *
        movingFrameComplexPolynomial g e p q (y,frameVector e y z.val)) =
      fun z : (UnitSphere N) => Complex.mk (eval (z.val : (I N) → ℝ) (Z*p)) (eval (z.val : (I N) → ℝ) (Z*q)) := by
    funext z
    rw [metricPair_frameVector g e y v.val z.val hframe,movingFrameComplexPolynomial_frameVector g e y hframe]
    simp only [Z, map_mul, eval_zonalPolynomial_of_unit _ _ (unitSphere_sum_sq z), ofReal_mul_complexMk]
  change (harmonicMultiplicity N m : ℂ) * (∫ z : (UnitSphere N),
      (zonal N (metricPair g y (frameVector e y v.val) (frameVector e y z.val)) m : ℂ) *
        movingFrameComplexPolynomial g e p q (y,frameVector e y z.val) ∂(unitSphereProbability N)) = _
  have hInt (a : MvPolynomial (I N) ℝ) :
      Integrable (fun z : UnitSphere N => eval (z.val : I N → ℝ) a) (unitSphereProbability N) :=
    (polynomialSphere a).continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  rw [hfun, integral_complexMk_of_integrable (hInt _) (hInt _), ← Complex.ofReal_natCast,
    ofReal_mul_complexMk]
  dsimp only [Z]
  have hpoly (z : UnitSphere N) := eval_zonalPolynomial_of_unit (v.val : I N → ℝ) (z.val : I N → ℝ)
    (unitSphere_sum_sq z) m
  simp_rw [map_mul, hpoly]
  rw [sphere_zonal_integral_eq_polynomial_inner,sphere_zonal_integral_eq_polynomial_inner]

variable {α : Type*}

lemma sphere_zonal_inner_family_projection (hn : 3 ≤ N) (v : (UnitSphere N)) (m : ℕ) (s : Finset α) (degree : α → ℕ)
    (p : α → MvPolynomial (I N) ℝ) (hp : ∀ i ∈ s, (p i).IsHomogeneous (degree i))
    (hΔ : ∀ i ∈ s, laplacian (p i) = 0) :
    (harmonicMultiplicity N m : ℝ)*⟪polynomialSphereL2 (zonalPolynomial (v.val : (I N) → ℝ) m),polynomialSphereL2 (∑ i ∈ s,p i)⟫_ℝ =
      ∑ i ∈ s, if m = degree i then eval (v.val : (I N) → ℝ) (p i) else 0 := by
  rw [map_sum,inner_sum,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [← sphere_zonal_integral_eq_polynomial_inner]
  exact sphere_zonal_projection_polynomial hn v m (degree i) (p i) (hp i hi) (hΔ i hi)

lemma sum_degree_indicator (s : Finset α) (degree : α → ℕ) (hinj : Set.InjOn degree (s : Set α))
    {i : α} (hi : i ∈ s) (f : α → ℝ) :
    (∑ j ∈ s,if degree i = degree j then f j else 0) = f i := by
  classical
  have hh : (∑ j ∈ s,if degree i = degree j then f j else 0) =
      if degree i = degree i then f i else 0 := by
    apply Finset.sum_eq_single i
    · intro j hj hji
      rw [if_neg (fun hd => hji (hinj hi hj hd).symm)]
    · intro hn
      exact False.elim (hn hi)
  simpa using hh

lemma degreePart_movingFrameComplexPolynomial_family (hn : 3 ≤ N) (g : (MetricField N)) (e : (Frame N)) (y : (X N))
    (hframe : ∀ i j, metricPair g y (e y i) (e y j) = if i = j then 1 else 0)
    (v : (UnitSphere N)) (m : ℕ) (s : Finset α) (degree : α → ℕ) (p q : α → MvPolynomial (I N) ℝ)
    (hp : ∀ i ∈ s, (p i).IsHomogeneous (degree i)) (hq : ∀ i ∈ s, (q i).IsHomogeneous (degree i))
    (hΔp : ∀ i ∈ s, laplacian (p i) = 0) (hΔq : ∀ i ∈ s, laplacian (q i) = 0) :
    degreePart g e m y (fun w => movingFrameComplexPolynomial g e (∑ i ∈ s,p i) (∑ i ∈ s,q i) (y,w)) (frameVector e y v.val) =
      Complex.mk (∑ i ∈ s,if m = degree i then eval (v.val : (I N) → ℝ) (p i) else 0)
        (∑ i ∈ s,if m = degree i then eval (v.val : (I N) → ℝ) (q i) else 0) := by
  rw [degreePart_movingFrameComplexPolynomial_frameVector_inner g e y hframe,
    sphere_zonal_inner_family_projection hn v m s degree p hp hΔp,
    sphere_zonal_inner_family_projection hn v m s degree q hq hΔq]

theorem fiberSq_degreePart_movingFrameComplexPolynomial_family (hn : 3 ≤ N) (g : (MetricField N)) (e : (Frame N)) (y : (X N))
    (hframe : ∀ i j, metricPair g y (e y i) (e y j) = if i = j then 1 else 0)
    (m : ℕ) (s : Finset α) (degree : α → ℕ) (hinj : Set.InjOn degree (s : Set α))
    (p q : α → MvPolynomial (I N) ℝ) (hp : ∀ i ∈ s, (p i).IsHomogeneous (degree i))
    (hq : ∀ i ∈ s, (q i).IsHomogeneous (degree i))
    (hΔp : ∀ i ∈ s, laplacian (p i) = 0) (hΔq : ∀ i ∈ s, laplacian (q i) = 0) :
    fiberSq e y (degreePart g e m y (fun w => movingFrameComplexPolynomial g e (∑ i ∈ s,p i) (∑ i ∈ s,q i) (y,w))) =
      ∑ i ∈ s,if m = degree i then (normalizedFischerSquare (degree i) (p i)+normalizedFischerSquare (degree i) (q i)) else 0 := by
  classical
  by_cases hm : ∃ i ∈ s,m = degree i
  · obtain ⟨i,hi,rfl⟩ := hm
    rw [sum_degree_indicator s degree hinj hi]
    calc
      _ = fiberSq e y (fun w => movingFrameComplexPolynomial g e (p i) (q i) (y,w)) := by
        apply fiberSq_congr_frameVector
        intro v
        rw [degreePart_movingFrameComplexPolynomial_family hn g e y hframe v _ s degree p q hp hq hΔp hΔq,
          sum_degree_indicator s degree hinj hi,sum_degree_indicator s degree hinj hi,
          movingFrameComplexPolynomial_frameVector g e y hframe]
      _ = _ := fiberSq_movingFrameComplexPolynomial g e y hframe _ _ (hp i hi) (hq i hi) (hΔp i hi) (hΔq i hi)
  · have hne (i : α) (hi : i ∈ s) : m ≠ degree i := fun heq => hm ⟨i,hi,heq⟩
    have hz (f : α → ℝ) : (∑ i ∈ s,if m = degree i then f i else 0) = 0 := by
      apply Finset.sum_eq_zero
      intro i hi
      rw [if_neg (hne i hi)]
    rw [hz]
    calc
      _ = fiberSq e y (fun _ => (0 : ℂ)) := by
        apply fiberSq_congr_frameVector
        intro v
        rw [degreePart_movingFrameComplexPolynomial_family hn g e y hframe v _ s degree p q hp hq hΔp hΔq,hz,hz]
        rfl
      _ = _ := fiberSq_zero e y

/-- The exact frozen Sobolev norm diagonalizes any finite family of distinct degrees. -/
theorem sobolevSq_movingFrameComplexPolynomial_family (hn : 3 ≤ N) (g : (MetricField N)) (e : (Frame N)) (y : (X N))
    (hframe : ∀ i j, metricPair g y (e y i) (e y j) = if i = j then 1 else 0)
    (a : ℝ) (s : Finset α) (degree : α → ℕ) (hinj : Set.InjOn degree (s : Set α))
    (p q : α → MvPolynomial (I N) ℝ) (hp : ∀ i ∈ s, (p i).IsHomogeneous (degree i))
    (hq : ∀ i ∈ s, (q i).IsHomogeneous (degree i))
    (hΔp : ∀ i ∈ s, laplacian (p i) = 0) (hΔq : ∀ i ∈ s, laplacian (q i) = 0) :
    sobolevSq g e a y (fun w => movingFrameComplexPolynomial g e (∑ i ∈ s,p i) (∑ i ∈ s,q i) (y,w)) =
      ∑ i ∈ s,(1+(degree i : ℝ))^(2*a)*(normalizedFischerSquare (degree i) (p i)+normalizedFischerSquare (degree i) (q i)) := by
  classical
  unfold sobolevSq
  simp_rw [fiberSq_degreePart_movingFrameComplexPolynomial_family hn g e y hframe _ s degree hinj p q hp hq hΔp hΔq]
  rw [tsum_eq_sum (s:=s.image degree)]
  · rw [Finset.sum_image (fun i hi j hj hd => hinj hi hj hd)]
    apply Finset.sum_congr rfl
    intro i hi
    rw [sum_degree_indicator s degree hinj hi]
  · intro m hm
    have hz : (∑ i ∈ s,if m = degree i then
        (normalizedFischerSquare (degree i) (p i)+normalizedFischerSquare (degree i) (q i)) else 0) = 0 := by
      apply Finset.sum_eq_zero
      intro i hi
      rw [if_neg (fun hd => hm (Finset.mem_image.mpr ⟨i,hi,hd.symm⟩))]
    rw [hz,mul_zero]

end CalderonN
