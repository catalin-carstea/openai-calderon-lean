import Proof.SpectralEnergyCoordinates

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open Set MeasureTheory MvPolynomial
open scoped ContDiff
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.SphereHarmonic

namespace HarmonicTestExpansion
variable {Y : Set X} {g : MetricField} {e : Frame} {φ : Field}

lemma partial_sobolevSquare (E : HarmonicTestExpansion Y g e φ)
    (hframe : ∀ y ∈ Y,∀ i j,metricPair g y (e y i) (e y j) = if i = j then 1 else 0)
    (s : ℝ) (n : ℕ) {y : X} (hy : y ∈ Y) :
    sobolevSq g e s y (fun w => E.partialField n (y,w)) =
      partialSobolevSquare s n (E.realSection y) (E.imagSection y) := by
  change sobolevSq g e s y (fun w => finiteAngularField g e (Finset.range n) E.basis E.realCoefficients E.imagCoefficients (y,w)) = _
  rw [sobolevSq_finiteAngularField g e y (hframe y hy) s (Finset.range n) (fun k => k+1)
    (fun k hk j hj heq => Nat.add_right_cancel heq) E.basis
    (fun k _ j => (E.basisHarmonic k j).1) (fun k _ j => (E.basisHarmonic k j).2)]
  unfold partialSobolevSquare
  exact Finset.sum_congr rfl (fun k _ => by rw [E.normalized_real_square,E.normalized_imag_square])

end HarmonicTestExpansion

namespace AngularModelData
variable {Y : Set X} {g : MetricField} {e : Frame} {φ : Field} {E : HarmonicTestExpansion Y g e φ} {r : X → ℝ}

lemma partial_horizontal_fiberSquare (D : AngularModelData E r)
    (hY : IsOpen Y) {K : ℝ} (h : Elliptic Y K g) (hK : 0 < K)
    (he : ∀ i,ContDiffOn ℝ ∞ (fun x => e x i) Y)
    (hframe : ∀ y ∈ Y,∀ i j,metricPair g y (e y i) (e y j) = if i = j then 1 else 0)
    (hφ : smoothNear φ (bundle Y g)) (n : ℕ) (i : I) {y : X} (hy : y ∈ Y) :
    fiberSq e y (fun w => horizontal g (E.partialField n) y w (e y i)) =
      partialSobolevSquare 0 n (D.realComponent.horizontalSection i y) (D.imagComponent.horizontalSection i y) := by
  change fiberSq e y (fun w => horizontal g (finiteAngularField g e (Finset.range n) E.basis E.realCoefficients E.imagCoefficients)
    y w (e y i)) = _
  rw [fiberSq_finiteAngularField_horizontal hY h hK e he hframe (Finset.range n) (fun k => k+1)
    (fun k _ => by omega) (fun k hk j hj heq => Nat.add_right_cancel heq) E.basis
    (fun k _ j => (E.basisHarmonic k j).1) (fun k _ j => (E.basisHarmonic k j).2) E.realCoefficients E.imagCoefficients
    (fun k _ => (E.realSmooth k).contDiffOn) (fun k _ => (E.imagSmooth k).contDiffOn) hy i]
  unfold partialSobolevSquare
  simp only [mul_zero,Real.rpow_zero,one_mul]
  apply Finset.sum_congr rfl
  intro k _
  have hr := D.realComponent.normalized_covariant_square hY h hK he hframe hφ k i hy
  have hi := D.imagComponent.normalized_covariant_square hY h hK he hframe hφ k i hy
  rw [realComponent_coordinates] at hr
  rw [imagComponent_coordinates] at hi
  rw [hr,hi]

lemma partial_horizontal_sobolevSquare (D : AngularModelData E r)
    (hY : IsOpen Y) {K : ℝ} (h : Elliptic Y K g) (hK : 0 < K)
    (he : ∀ i,ContDiffOn ℝ ∞ (fun x => e x i) Y)
    (hframe : ∀ y ∈ Y,∀ i j,metricPair g y (e y i) (e y j) = if i = j then 1 else 0)
    (hφ : smoothNear φ (bundle Y g)) (s : ℝ) (n : ℕ) (i : I) {y : X} (hy : y ∈ Y) :
    sobolevSq g e s y (fun w => horizontal g (E.partialField n) y w (e y i)) =
      partialSobolevSquare s n (D.realComponent.horizontalSection i y) (D.imagComponent.horizontalSection i y) := by
  change sobolevSq g e s y (fun w => horizontal g (finiteAngularField g e (Finset.range n) E.basis E.realCoefficients E.imagCoefficients)
    y w (e y i)) = _
  rw [sobolevSq_finiteAngularField_horizontal hY h hK e he hframe s (Finset.range n) (fun k => k+1)
    (fun k _ => by omega) (fun k hk j hj heq => Nat.add_right_cancel heq) E.basis
    (fun k _ j => (E.basisHarmonic k j).1) (fun k _ j => (E.basisHarmonic k j).2) E.realCoefficients E.imagCoefficients
    (fun k _ => (E.realSmooth k).contDiffOn) (fun k _ => (E.imagSmooth k).contDiffOn) hy i]
  unfold partialSobolevSquare
  apply Finset.sum_congr rfl
  intro k _
  have hr := D.realComponent.normalized_covariant_square hY h hK he hframe hφ k i hy
  have hi := D.imagComponent.normalized_covariant_square hY h hK he hframe hφ k i hy
  rw [realComponent_coordinates] at hr
  rw [imagComponent_coordinates] at hi
  rw [hr,hi]

end AngularModelData
end ShrinkingSpheres
