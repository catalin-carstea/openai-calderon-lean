import Proof.ModelPolynomialCoefficients
import Proof.AngularOutputSums

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open Set MeasureTheory MvPolynomial Filter
open scoped ContDiff
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.AngularPolynomial
open OAI.AnisotropicCalderon.SphereHarmonic
open OAI.AnisotropicCalderon.HarmonicDerivativeOperator

lemma fiberSq_polynomial_L2 (g : MetricField) (e : Frame) (y : X)
    (hframe : ∀ i j,metricPair g y (e y i) (e y j) = if i = j then 1 else 0)
    (p q : MvPolynomial I ℝ) :
    fiberSq e y (fun w => movingFrameComplexPolynomial g e p q (y,w)) =
      ‖polynomialSphereL2 p‖^2+‖polynomialSphereL2 q‖^2 := by
  apply fiberSq_eq_component_norms e y _ (polynomialSphereL2 p) (polynomialSphereL2 q)
  · apply ((polynomialSphere p).coeFn_toLp (p:=2) (𝕜:=ℝ) sphereProbability).trans
    exact Filter.Eventually.of_forall (fun v => by
      dsimp only
      rw [movingFrameComplexPolynomial_frameVector g e y hframe]
      rfl)
  · apply ((polynomialSphere q).coeFn_toLp (p:=2) (𝕜:=ℝ) sphereProbability).trans
    exact Filter.Eventually.of_forall (fun v => by
      dsimp only
      rw [movingFrameComplexPolynomial_frameVector g e y hframe]
      rfl)

lemma polynomialSphereL2_raised_eq_projection {Y : Set X} (hY : IsOpen Y) {K : ℝ} {g : MetricField}
    (h : Elliptic Y K g) (hK : 0 < K) (e : Frame)
    (he : ∀ i,ContDiffOn ℝ ∞ (fun x => e x i) Y)
    (hframe : ∀ y ∈ Y,∀ i j,metricPair g y (e y i) (e y j) = if i = j then 1 else 0)
    {ι : Type*} [Fintype ι] (k : ℕ) (basis : ι → MvPolynomial I ℝ)
    (hb : ∀ j,basis j ∈ harmonicHomogeneous (k+1)) (c : X → ι → ℝ) (f : X → ℝ)
    (H : I → X × X → ℝ) (G : X × X → ℝ) (hH : ∀ i,ContDiff ℝ ∞ (H i)) (hG : ContDiff ℝ ∞ G)
    (b : I → X → ℝ) {y : X} (hy : y ∈ Y)
    (hrep : ∀ i,polynomialSphereL2 (weightedFramePolynomialField g e basis c f (k+1) 1 y i) =
      (harmonicProjection (k+1) (weightedAngularSection (H i) G (hH i) hG (b i) 1 y) : SphereL2)) :
    polynomialSphereL2 (raisedPolynomialField g e basis c f k y) =
      (harmonicProjection (k+2) (angularRaisingSum H G hH hG b y) : SphereL2) := by
  have hq (i : I) : weightedFramePolynomialField g e basis c f (k+1) 1 y i ∈ harmonicHomogeneous (k+1) := by
    refine ⟨?_,weightedFramePolynomialField_harmonic hY h hK e he hframe basis (fun j => (hb j).2) c f (k+1) 1 hy i⟩
    simpa only [weightedFramePolynomialField,Nat.cast_add,Nat.cast_one] using
      weightedPolynomialDerivative_homogeneous (by omega) g e basis (fun j => (hb j).1) c f 1 y (e y i)
  rw [raisedPolynomialField,polynomialSphereL2_raising_eq k _ hq _ hrep,
    harmonicProjection_angularRaisingSum_succ H G hH hG b y (k+1)]
  simp only [Submodule.coe_sum]

lemma polynomialSphereL2_lowered_eq_projection {Y : Set X} (hY : IsOpen Y) {K : ℝ} {g : MetricField}
    (h : Elliptic Y K g) (hK : 0 < K) (e : Frame)
    (he : ∀ i,ContDiffOn ℝ ∞ (fun x => e x i) Y)
    (hframe : ∀ y ∈ Y,∀ i j,metricPair g y (e y i) (e y j) = if i = j then 1 else 0)
    {ι : Type*} [Fintype ι] (k : ℕ) (basis : ι → MvPolynomial I ℝ)
    (hb : ∀ j,basis j ∈ harmonicHomogeneous (k+1)) (c : X → ι → ℝ) (f : X → ℝ)
    (H : I → X × X → ℝ) (G : X × X → ℝ) (hH : ∀ i,ContDiff ℝ ∞ (H i)) (hG : ContDiff ℝ ∞ G)
    (b : I → X → ℝ) {y : X} (hy : y ∈ Y)
    (hrep : ∀ i,polynomialSphereL2 (weightedFramePolynomialField g e basis c f (k+1) (-1) y i) =
      (harmonicProjection (k+1) (weightedAngularSection (H i) G (hH i) hG (b i) (-1) y) : SphereL2)) :
    polynomialSphereL2 (loweredPolynomialField g e basis c f k y) =
      (harmonicProjection k (angularLoweringSum H G hH hG b y) : SphereL2) := by
  have hq (i : I) : weightedFramePolynomialField g e basis c f (k+1) (-1) y i ∈ harmonicHomogeneous (k+1) := by
    refine ⟨?_,weightedFramePolynomialField_harmonic hY h hK e he hframe basis (fun j => (hb j).2) c f (k+1) (-1) hy i⟩
    simpa only [weightedFramePolynomialField,Nat.cast_add,Nat.cast_one] using
      weightedPolynomialDerivative_homogeneous (by omega) g e basis (fun j => (hb j).1) c f (-1) y (e y i)
  rw [loweredPolynomialField,polynomialSphereL2_lowering_eq k _ hq _ hrep,
    harmonicProjection_angularLoweringSum H G hH hG b y k]
  simp only [Submodule.coe_sum]

lemma harmonicPartialSum_eq_shift_two (n : ℕ) (u : SphereL2)
    (h₀ : harmonicProjection 0 u = 0) (h₁ : harmonicProjection 1 u = 0) :
    harmonicPartialSum (n+2) u = ∑ k ∈ Finset.range n,(harmonicProjection (k+2) u : SphereL2) := by
  rw [harmonicPartialSum_eq_sum,Finset.sum_range_succ',Finset.sum_range_succ']
  simp only [h₀,h₁,Submodule.coe_zero,add_zero]

end ShrinkingSpheres
