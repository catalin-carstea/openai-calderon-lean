import Proof.ComplexPolynomialTests

noncomputable section
set_option autoImplicit false
open Set MeasureTheory MvPolynomial
open scoped InnerProductSpace
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.AngularPolynomial
open OAI.AnisotropicCalderon.SphereHarmonic

variable {α : Type*}

lemma polynomialSphereL2_family_pythagoras (s : Finset α) (degree : α → ℕ)
    (hinj : Set.InjOn degree (s : Set α)) (p : α → MvPolynomial I ℝ)
    (hp : ∀ i ∈ s, (p i).IsHomogeneous (degree i)) (hΔ : ∀ i ∈ s, laplacian (p i) = 0) :
    ‖polynomialSphereL2 (∑ i ∈ s, p i)‖^2 = ∑ i ∈ s, normalizedFischerSquare (degree i) (p i) := by
  classical
  rw [map_sum, ← real_inner_self_eq_norm_sq, sum_inner]
  apply Finset.sum_congr rfl
  intro i hi
  rw [inner_sum]
  have hdiag : (∑ j ∈ s, ⟪polynomialSphereL2 (p i), polynomialSphereL2 (p j)⟫_ℝ) =
      ⟪polynomialSphereL2 (p i), polynomialSphereL2 (p i)⟫_ℝ := by
    apply Finset.sum_eq_single i
    · intro j hj hji
      exact orthogonalSphereHarmonics (degree i) (degree j)
        (fun hd => hji (hinj hi hj hd).symm) _
        (polynomialSphereL2_mem _ _ ⟨hp i hi,hΔ i hi⟩) _
        (polynomialSphereL2_mem _ _ ⟨hp j hj,hΔ j hj⟩)
    · intro hn
      exact False.elim (hn hi)
  rw [hdiag, sphereFischerInner (degree i) _ _ ⟨hp i hi,hΔ i hi⟩ ⟨hp i hi,hΔ i hi⟩]
  rfl

lemma fiberSq_movingFramePolynomial_eq_L2 (g : MetricField) (e : Frame) (y : X)
    (hframe : ∀ i j, metricPair g y (e y i) (e y j) = if i = j then 1 else 0) (p : MvPolynomial I ℝ) :
    fiberSq e y (fun w => (movingFramePolynomial g e p (y,w) : ℂ)) = ‖polynomialSphereL2 p‖^2 := by
  rw [fiberSq_ofReal, ← real_inner_self_eq_norm_sq, polynomialSphereL2_inner]
  simp_rw [movingFramePolynomial_frameVector g e y hframe]
  simp only [pow_two]
  rfl

/-- The complex fiber square splits into its two real components for every polynomial,
    including finite sums of different degrees. -/
lemma fiberSq_movingFrameComplexPolynomial_split (g : MetricField) (e : Frame) (y : X)
    (hframe : ∀ i j, metricPair g y (e y i) (e y j) = if i = j then 1 else 0) (p q : MvPolynomial I ℝ) :
    fiberSq e y (fun w => movingFrameComplexPolynomial g e p q (y,w)) =
      fiberSq e y (fun w => (movingFramePolynomial g e p (y,w) : ℂ)) +
        fiberSq e y (fun w => (movingFramePolynomial g e q (y,w) : ℂ)) := by
  have hPInt : Integrable (fun w : UnitSphere => (eval (w.val : I → ℝ) p)^2) sphereProbability :=
    ((polynomialSphere p).continuous.pow 2).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hQInt : Integrable (fun w : UnitSphere => (eval (w.val : I → ℝ) q)^2) sphereProbability :=
    ((polynomialSphere q).continuous.pow 2).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  rw [fiberSq_integral_norm, fiberSq_ofReal, fiberSq_ofReal]
  simp_rw [movingFrameComplexPolynomial_frameVector g e y hframe, movingFramePolynomial_frameVector g e y hframe,
    Complex.sq_norm, Complex.normSq_mk]
  simp only [pow_two] at hPInt hQInt ⊢
  change (∫ w : UnitSphere, eval (w.val : I → ℝ) p * eval (w.val : I → ℝ) p +
    eval (w.val : I → ℝ) q * eval (w.val : I → ℝ) q ∂sphereProbability) = _
  exact integral_add hPInt hQInt

/-- Physical complex Pythagoras for any finite family of distinct harmonic degrees. -/
theorem fiberSq_movingFrameComplexPolynomial_family (g : MetricField) (e : Frame) (y : X)
    (hframe : ∀ i j, metricPair g y (e y i) (e y j) = if i = j then 1 else 0)
    (s : Finset α) (degree : α → ℕ) (hinj : Set.InjOn degree (s : Set α))
    (p q : α → MvPolynomial I ℝ) (hp : ∀ i ∈ s, (p i).IsHomogeneous (degree i))
    (hq : ∀ i ∈ s, (q i).IsHomogeneous (degree i))
    (hΔp : ∀ i ∈ s, laplacian (p i) = 0) (hΔq : ∀ i ∈ s, laplacian (q i) = 0) :
    fiberSq e y (fun w => movingFrameComplexPolynomial g e (∑ i ∈ s, p i) (∑ i ∈ s, q i) (y,w)) =
      ∑ i ∈ s, (normalizedFischerSquare (degree i) (p i)+normalizedFischerSquare (degree i) (q i)) := by
  rw [fiberSq_movingFrameComplexPolynomial_split g e y hframe,
    fiberSq_movingFramePolynomial_eq_L2 g e y hframe, fiberSq_movingFramePolynomial_eq_L2 g e y hframe,
    polynomialSphereL2_family_pythagoras s degree hinj p hp hΔp,
    polynomialSphereL2_family_pythagoras s degree hinj q hq hΔq, Finset.sum_add_distrib]

end ShrinkingSpheres
