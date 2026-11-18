import Proof.AngularComponentData

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open Set MeasureTheory Filter
open scoped ContDiff
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.SphereHarmonic

namespace AngularModelData
variable {Y : Set X} {g : MetricField} {e : Frame} {φ : Field} {E : HarmonicTestExpansion Y g e φ} {r : X → ℝ}

theorem fiberSq_finiteRaised_eq_partial (D : AngularModelData E r)
    (hY : IsOpen Y) {K : ℝ} (h : Elliptic Y K g) (hK : 0 < K)
    (he : ∀ i,ContDiffOn ℝ ∞ (fun x => e x i) Y)
    (hframe : ∀ y ∈ Y,∀ i j,metricPair g y (e y i) (e y j) = if i = j then 1 else 0)
    (hφ : smoothNear φ (bundle Y g)) (n : ℕ) {y : X} (hy : y ∈ Y) :
    fiberSq e y (fun w => finiteRaisedField g e (Finset.range n) id E.basis E.realCoefficients E.imagCoefficients
      (fun x => Real.log (r x)) (y,w)) =
      ‖harmonicPartialSum (n+2) (D.realComponent.raisingOutput y)‖^2+
        ‖harmonicPartialSum (n+2) (D.imagComponent.raisingOutput y)‖^2 := by
  change fiberSq e y (fun w => movingFrameComplexPolynomial g e
    (∑ k ∈ Finset.range n,raisedPolynomialField g e (E.basis k) (E.realCoefficients k) (fun x => Real.log (r x)) k y)
    (∑ k ∈ Finset.range n,raisedPolynomialField g e (E.basis k) (E.imagCoefficients k) (fun x => Real.log (r x)) k y) (y,w)) = _
  rw [fiberSq_polynomial_L2 g e y (hframe y hy)]
  have hr := D.realComponent.raising_sum_partial hY h hK he hframe hφ n hy
  have hi := D.imagComponent.raising_sum_partial hY h hK he hframe hφ n hy
  rw [realComponent_coordinates] at hr
  rw [imagComponent_coordinates] at hi
  rw [hr,hi]

theorem fiberSq_finiteLowered_eq_partial (D : AngularModelData E r)
    (hY : IsOpen Y) {K : ℝ} (h : Elliptic Y K g) (hK : 0 < K)
    (he : ∀ i,ContDiffOn ℝ ∞ (fun x => e x i) Y)
    (hframe : ∀ y ∈ Y,∀ i j,metricPair g y (e y i) (e y j) = if i = j then 1 else 0)
    (hφ : smoothNear φ (bundle Y g)) (n : ℕ) {y : X} (hy : y ∈ Y) :
    fiberSq e y (fun w => finiteLoweredField g e (Finset.range n) id E.basis E.realCoefficients E.imagCoefficients
      (fun x => Real.log (r x)) (y,w)) =
      ‖harmonicPartialSum n (D.realComponent.loweringOutput y)‖^2+
        ‖harmonicPartialSum n (D.imagComponent.loweringOutput y)‖^2 := by
  change fiberSq e y (fun w => movingFrameComplexPolynomial g e
    (∑ k ∈ Finset.range n,loweredPolynomialField g e (E.basis k) (E.realCoefficients k) (fun x => Real.log (r x)) k y)
    (∑ k ∈ Finset.range n,loweredPolynomialField g e (E.basis k) (E.imagCoefficients k) (fun x => Real.log (r x)) k y) (y,w)) = _
  rw [fiberSq_polynomial_L2 g e y (hframe y hy)]
  have hr := D.realComponent.lowering_sum_partial hY h hK he hframe hφ n hy
  have hi := D.imagComponent.lowering_sum_partial hY h hK he hframe hφ n hy
  rw [realComponent_coordinates] at hr
  rw [imagComponent_coordinates] at hi
  rw [hr,hi]

end AngularModelData
end ShrinkingSpheres
