import Proof.FiniteAngularPythagoras

noncomputable section
set_option autoImplicit false
open Set MeasureTheory MvPolynomial
open scoped InnerProductSpace
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.AngularPolynomial
open OAI.AnisotropicCalderon.SphereHarmonic

lemma degreePart_movingFrameComplexPolynomial_frameVector_inner (g : MetricField) (e : Frame) (y : X)
    (hframe : ∀ i j, metricPair g y (e y i) (e y j) = if i = j then 1 else 0)
    (v : UnitSphere) (m : ℕ) (p q : MvPolynomial I ℝ) :
    degreePart g e m y (fun w => movingFrameComplexPolynomial g e p q (y,w)) (frameVector e y v.val) =
      Complex.mk ((2*(m : ℝ)+1)*⟪polynomialSphereL2 (zonalPolynomial (v.val : I → ℝ) m),polynomialSphereL2 p⟫_ℝ)
        ((2*(m : ℝ)+1)*⟪polynomialSphereL2 (zonalPolynomial (v.val : I → ℝ) m),polynomialSphereL2 q⟫_ℝ) := by
  let Z := zonalPolynomial (v.val : I → ℝ) m
  have hfun : (fun z : UnitSphere =>
      (legendre (metricPair g y (frameVector e y v.val) (frameVector e y z.val)) m : ℂ) *
        movingFrameComplexPolynomial g e p q (y,frameVector e y z.val)) =
      fun z : UnitSphere => Complex.mk (eval (z.val : I → ℝ) (Z*p)) (eval (z.val : I → ℝ) (Z*q)) := by
    funext z
    rw [metricPair_frameVector g e y v.val z.val hframe,movingFrameComplexPolynomial_frameVector g e y hframe]
    simp only [Z,map_mul,eval_zonalPolynomial_unitSphere,ofReal_mul_complexMk]
  change (((2*(m : ℝ)+1) : ℝ) : ℂ) * (∫ z : UnitSphere,
      (legendre (metricPair g y (frameVector e y v.val) (frameVector e y z.val)) m : ℂ) *
        movingFrameComplexPolynomial g e p q (y,frameVector e y z.val) ∂sphereProbability) = _
  rw [hfun,integral_complexPolynomialSphere,ofReal_mul_complexMk]
  dsimp only [Z]
  simp_rw [map_mul,eval_zonalPolynomial_unitSphere]
  rw [sphere_legendre_integral_eq_inner,sphere_legendre_integral_eq_inner]

variable {α : Type*}

lemma sphere_legendre_inner_family_projection (v : UnitSphere) (m : ℕ) (s : Finset α) (degree : α → ℕ)
    (p : α → MvPolynomial I ℝ) (hp : ∀ i ∈ s, (p i).IsHomogeneous (degree i))
    (hΔ : ∀ i ∈ s, laplacian (p i) = 0) :
    (2*(m : ℝ)+1)*⟪polynomialSphereL2 (zonalPolynomial (v.val : I → ℝ) m),polynomialSphereL2 (∑ i ∈ s,p i)⟫_ℝ =
      ∑ i ∈ s, if m = degree i then eval (v.val : I → ℝ) (p i) else 0 := by
  rw [map_sum,inner_sum,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  exact sphere_legendre_inner_projection v m (degree i) (p i) (hp i hi) (hΔ i hi)

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

lemma degreePart_movingFrameComplexPolynomial_family (g : MetricField) (e : Frame) (y : X)
    (hframe : ∀ i j, metricPair g y (e y i) (e y j) = if i = j then 1 else 0)
    (v : UnitSphere) (m : ℕ) (s : Finset α) (degree : α → ℕ) (p q : α → MvPolynomial I ℝ)
    (hp : ∀ i ∈ s, (p i).IsHomogeneous (degree i)) (hq : ∀ i ∈ s, (q i).IsHomogeneous (degree i))
    (hΔp : ∀ i ∈ s, laplacian (p i) = 0) (hΔq : ∀ i ∈ s, laplacian (q i) = 0) :
    degreePart g e m y (fun w => movingFrameComplexPolynomial g e (∑ i ∈ s,p i) (∑ i ∈ s,q i) (y,w)) (frameVector e y v.val) =
      Complex.mk (∑ i ∈ s,if m = degree i then eval (v.val : I → ℝ) (p i) else 0)
        (∑ i ∈ s,if m = degree i then eval (v.val : I → ℝ) (q i) else 0) := by
  rw [degreePart_movingFrameComplexPolynomial_frameVector_inner g e y hframe,
    sphere_legendre_inner_family_projection v m s degree p hp hΔp,
    sphere_legendre_inner_family_projection v m s degree q hq hΔq]

theorem fiberSq_degreePart_movingFrameComplexPolynomial_family (g : MetricField) (e : Frame) (y : X)
    (hframe : ∀ i j, metricPair g y (e y i) (e y j) = if i = j then 1 else 0)
    (m : ℕ) (s : Finset α) (degree : α → ℕ) (hinj : Set.InjOn degree (s : Set α))
    (p q : α → MvPolynomial I ℝ) (hp : ∀ i ∈ s, (p i).IsHomogeneous (degree i))
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
        rw [degreePart_movingFrameComplexPolynomial_family g e y hframe v _ s degree p q hp hq hΔp hΔq,
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
        rw [degreePart_movingFrameComplexPolynomial_family g e y hframe v _ s degree p q hp hq hΔp hΔq,hz,hz]
        rfl
      _ = _ := fiberSq_zero e y

/-- The exact frozen Sobolev norm diagonalizes any finite family of distinct degrees. -/
theorem sobolevSq_movingFrameComplexPolynomial_family (g : MetricField) (e : Frame) (y : X)
    (hframe : ∀ i j, metricPair g y (e y i) (e y j) = if i = j then 1 else 0)
    (a : ℝ) (s : Finset α) (degree : α → ℕ) (hinj : Set.InjOn degree (s : Set α))
    (p q : α → MvPolynomial I ℝ) (hp : ∀ i ∈ s, (p i).IsHomogeneous (degree i))
    (hq : ∀ i ∈ s, (q i).IsHomogeneous (degree i))
    (hΔp : ∀ i ∈ s, laplacian (p i) = 0) (hΔq : ∀ i ∈ s, laplacian (q i) = 0) :
    sobolevSq g e a y (fun w => movingFrameComplexPolynomial g e (∑ i ∈ s,p i) (∑ i ∈ s,q i) (y,w)) =
      ∑ i ∈ s,(1+(degree i : ℝ))^(2*a)*(normalizedFischerSquare (degree i) (p i)+normalizedFischerSquare (degree i) (q i)) := by
  classical
  unfold sobolevSq
  simp_rw [fiberSq_degreePart_movingFrameComplexPolynomial_family g e y hframe _ s degree hinj p q hp hq hΔp hΔq]
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

end ShrinkingSpheres
