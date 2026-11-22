module

public import Proof.CalderonN.ModelPolynomialCoefficients
public import Proof.CalderonN.SmoothBesselSections
public import Proof.CalderonN.SphereRaisingEnergy
import Mathlib.Tactic

@[expose] public section

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open Set MeasureTheory MvPolynomial Filter
open scoped ContDiff
namespace CalderonN

variable {dim : ℕ} [NeZero dim]
open OAI.AnisotropicCalderon.AngularPolynomial
open OAI.AnisotropicCalderon.SphereHarmonic

lemma fiberSq_polynomial_L2 (g : (MetricField dim)) (e : (Frame dim)) (y : (X dim))
    (hframe : ∀ i j,metricPair g y (e y i) (e y j) = if i = j then 1 else 0)
    (p q : MvPolynomial (I dim) ℝ) :
    fiberSq e y (fun w => movingFrameComplexPolynomial g e p q (y,w)) =
      ‖polynomialSphereL2 p‖^2+‖polynomialSphereL2 q‖^2 := by
  apply fiberSq_eq_component_norms e y _ (polynomialSphereL2 p) (polynomialSphereL2 q)
  · change (⇑(polynomialSphereL2 p)) =ᵐ[unitSphereProbability dim] _
    apply ((polynomialSphere p).coeFn_toLp (p:=2) (𝕜:=ℝ) (unitSphereProbability dim)).trans
    exact Filter.Eventually.of_forall (fun v => by
      dsimp only
      rw [movingFrameComplexPolynomial_frameVector g e y hframe]
      rfl)
  · change (⇑(polynomialSphereL2 q)) =ᵐ[unitSphereProbability dim] _
    apply ((polynomialSphere q).coeFn_toLp (p:=2) (𝕜:=ℝ) (unitSphereProbability dim)).trans
    exact Filter.Eventually.of_forall (fun v => by
      dsimp only
      rw [movingFrameComplexPolynomial_frameVector g e y hframe]
      rfl)

private theorem polynomialSphereRaising_eq_sum_adjoint (k : ℕ)
    (q : I dim → MvPolynomial (I dim) ℝ) :
    polynomialSphereRaising k q = ∑ i, sphereDerivativeAdjoint (k+1) i (q i) := by
  have hq : (fun i => ∑ j, (Pi.single j (q j) : I dim → MvPolynomial (I dim) ℝ) i) = q := by
    funext i
    simp [Pi.single_apply]
  calc
    polynomialSphereRaising k q =
        polynomialSphereRaising k (fun i => ∑ j, (Pi.single j (q j) : I dim → MvPolynomial (I dim) ℝ) i) :=
      congrArg (polynomialSphereRaising k) hq.symm
    _ = _ := by rw [polynomialSphereRaising_sum_family]; rfl

private theorem harmonicPolynomialSphereMap_eq (k : ℕ) (p : MvPolynomial (I dim) ℝ)
    (hp : p ∈ harmonicHomogeneous dim k) (u : harmonicSphereSubspace dim k)
    (hrep : polynomialSphereL2 p = (u : SphereL2 dim)) :
    harmonicPolynomialSphereMap k ⟨p,hp⟩ = u := Subtype.ext hrep

lemma polynomialSphereL2_raised_eq_projection (hn : 3 ≤ dim) {Y : Set (X dim)} (hY : IsOpen Y) {K : ℝ} {g : (MetricField dim)}
    (h : Elliptic Y K g) (hK : 0 < K) (e : (Frame dim))
    (he : ∀ i,ContDiffOn ℝ ∞ (fun x => e x i) Y)
    (hframe : ∀ y ∈ Y,∀ i j,metricPair g y (e y i) (e y j) = if i = j then 1 else 0)
    {ι : Type*} [Fintype ι] (k : ℕ) (basis : ι → MvPolynomial (I dim) ℝ)
    (hb : ∀ j,basis j ∈ harmonicHomogeneous dim (k+1)) (c : (X dim) → ι → ℝ) (f : (X dim) → ℝ)
    (H : (I dim) → (X dim) × (X dim) → ℝ) (G : (X dim) × (X dim) → ℝ) (hH : ∀ i,ContDiff ℝ ∞ (H i)) (hG : ContDiff ℝ ∞ G)
    (b : (I dim) → (X dim) → ℝ) {y : (X dim)} (hy : y ∈ Y)
    (hrep : ∀ i,polynomialSphereL2 (weightedFramePolynomialField g e basis c f (k+1) 1 y i) =
      (weightedAngularComponent (H i) G (hH i) hG (b i) 1 y (k+1) : (SphereL2 dim))) :
    polynomialSphereL2 (raisedPolynomialField g e basis c f k y) =
      (harmonicProjection (k+2) (angularRaisingSum hn H G hH hG b y) : (SphereL2 dim)) := by
  have hq (i : (I dim)) : weightedFramePolynomialField g e basis c f (k+1) 1 y i ∈ harmonicHomogeneous dim (k+1) := by
    refine ⟨?_,weightedFramePolynomialField_harmonic hY h hK e he hframe basis (fun j => (hb j).2) c f (k+1) 1 hy i⟩
    simpa only [weightedFramePolynomialField,Nat.cast_add,Nat.cast_one] using
      weightedPolynomialDerivative_homogeneous (by omega) g e basis (fun j => (hb j).1) c f 1 y (e y i)
  rw [raisedPolynomialField, polynomialSphereRaising_eq_sum_adjoint, map_sum,
    harmonicProjection_angularRaisingSum_succ hn H G hH hG b y (k+1), Submodule.coe_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← harmonicPolynomialSphereMap_eq (k+1) _ (hq i) _ (hrep i),
    harmonicDerivativeAdjoint_apply_image]
  rfl

lemma polynomialSphereL2_lowered_eq_projection (hn : 3 ≤ dim) {Y : Set (X dim)} (hY : IsOpen Y) {K : ℝ} {g : (MetricField dim)}
    (h : Elliptic Y K g) (hK : 0 < K) (e : (Frame dim))
    (he : ∀ i,ContDiffOn ℝ ∞ (fun x => e x i) Y)
    (hframe : ∀ y ∈ Y,∀ i j,metricPair g y (e y i) (e y j) = if i = j then 1 else 0)
    {ι : Type*} [Fintype ι] (k : ℕ) (basis : ι → MvPolynomial (I dim) ℝ)
    (hb : ∀ j,basis j ∈ harmonicHomogeneous dim (k+1)) (c : (X dim) → ι → ℝ) (f : (X dim) → ℝ)
    (H : (I dim) → (X dim) × (X dim) → ℝ) (G : (X dim) × (X dim) → ℝ) (hH : ∀ i,ContDiff ℝ ∞ (H i)) (hG : ContDiff ℝ ∞ G)
    (b : (I dim) → (X dim) → ℝ) {y : (X dim)} (hy : y ∈ Y)
    (hrep : ∀ i,polynomialSphereL2 (weightedFramePolynomialField g e basis c f (k+1) (-1) y i) =
      (weightedAngularComponent (H i) G (hH i) hG (b i) (-1) y (k+1) : (SphereL2 dim))) :
    polynomialSphereL2 (loweredPolynomialField g e basis c f k y) =
      (harmonicProjection k (angularLoweringSum hn H G hH hG b y) : (SphereL2 dim)) := by
  have hq (i : (I dim)) : weightedFramePolynomialField g e basis c f (k+1) (-1) y i ∈ harmonicHomogeneous dim (k+1) := by
    refine ⟨?_,weightedFramePolynomialField_harmonic hY h hK e he hframe basis (fun j => (hb j).2) c f (k+1) (-1) hy i⟩
    simpa only [weightedFramePolynomialField,Nat.cast_add,Nat.cast_one] using
      weightedPolynomialDerivative_homogeneous (by omega) g e basis (fun j => (hb j).1) c f (-1) y (e y i)
  rw [loweredPolynomialField, polynomialDivergence, map_sum,
    harmonicProjection_angularLoweringSum hn H G hH hG b y k, Submodule.coe_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← harmonicPolynomialSphereMap_eq (k+1) _ (hq i) _ (hrep i),
    harmonicDerivative_apply_image]
  rfl

lemma harmonicPartialSum_eq_shift_two (n : ℕ) (u : (SphereL2 dim))
    (h₀ : harmonicProjection 0 u = 0) (h₁ : harmonicProjection 1 u = 0) :
    harmonicPartialSum (n+2) u = ∑ k ∈ Finset.range n,(harmonicProjection (k+2) u : (SphereL2 dim)) := by
  rw [harmonicPartialSum_apply,Finset.sum_range_succ',Finset.sum_range_succ']
  simp only [h₀,h₁,Submodule.coe_zero,add_zero]

end CalderonN
