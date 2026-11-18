import Proof.PartialSobolevSquares

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open Set MeasureTheory MvPolynomial Filter
open scoped ContDiff
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.AngularPolynomial
open OAI.AnisotropicCalderon.SphereHarmonic
open OAI.AnisotropicCalderon.SmoothSphereFields

lemma normalizedFischerSquare_eq_projection_norm (k : ℕ) (p : MvPolynomial I ℝ)
    (hp : p ∈ harmonicHomogeneous k) (u : SphereL2)
    (hrep : polynomialSphereL2 p = (harmonicProjection k u : SphereL2)) :
    normalizedFischerSquare k p = ‖harmonicProjection k u‖^2 := by
  rw [← polynomialSphereL2_norm_sq sphereFischerInner k p hp,hrep]
  rfl

namespace AngularComponentData
variable {Y : Set X} {g : MetricField} {e : Frame} {φ : Field} {E : HarmonicTestExpansion Y g e φ}
  {r : X → ℝ} {L : ℂ →L[ℝ] ℝ}

def horizontalSection (Q : AngularComponentData E r L) (i : I) : X → SphereL2 :=
  ambientSphereL2 (Q.horizontalRepresentative i) (Q.horizontalSmooth i)

lemma horizontalSection_ae (Q : AngularComponentData E r L) (i : I) {y : X} (hy : y ∈ Y) :
    Q.horizontalSection i y =ᵐ[sphereProbability]
      (fun v : UnitSphere => L (horizontal g φ y (frameVector e y v.val) (e y i))) := by
  apply (ambientSphereL2_ae _ _ y).trans
  exact Filter.Eventually.of_forall (fun v => Q.horizontalEq i y hy v)

lemma horizontalSection_zeroDegree (Q : AngularComponentData E r L)
    (hY : IsOpen Y) {K : ℝ} (h : Elliptic Y K g) (hK : 0 < K)
    (he : ∀ i,ContDiffOn ℝ ∞ (fun x => e x i) Y)
    (hframe : ∀ y ∈ Y,∀ i j,metricPair g y (e y i) (e y j) = if i = j then 1 else 0)
    (hφ : smoothNear φ (bundle Y g)) (i : I) {y : X} (hy : y ∈ Y) :
    harmonicProjection 0 (Q.horizontalSection i y) = 0 :=
  E.horizontal_zeroDegree_component hY h hK he hframe hφ L Q.zeroDegree hy (e y i) _ (Q.horizontalSection_ae i hy)

lemma covariant_polynomial_L2 (Q : AngularComponentData E r L)
    (hY : IsOpen Y) {K : ℝ} (h : Elliptic Y K g) (hK : 0 < K)
    (he : ∀ i,ContDiffOn ℝ ∞ (fun x => e x i) Y)
    (hframe : ∀ y ∈ Y,∀ i j,metricPair g y (e y i) (e y j) = if i = j then 1 else 0)
    (hφ : smoothNear φ (bundle Y g)) (k : ℕ) (i : I) {y : X} (hy : y ∈ Y) :
    polynomialSphereL2 (covariantPolynomialDerivative g e (E.basis k) (Q.coordinates k) y (e y i)) =
      (harmonicProjection (k+1) (Q.horizontalSection i y) : SphereL2) := by
  have hU : ContDiff ℝ ∞ (fun x => harmonicProjection (k+1)
      (ambientSphereL2 (fun p => L (E.representative p)) (L.contDiff.comp E.representativeSmooth) x)) :=
    (harmonicProjection (k+1)).contDiff.comp (contDiff_ambientSphereL2 _ _)
  rw [polynomialSphereL2_covariantDerivative hY h hK e he hframe (k+1) (E.basis k)
    (E.basisHarmonic k) (Q.coordinates k) _ (Q.coordinatesSmooth k) hU (Q.coordinatesEq k) hy (e y i),
    harmonicProjection_horizontal_component hY h hK e he hframe φ hφ E.representative
      E.representativeSmooth E.representativeEq L hy (e y i) (Q.horizontalSection i y) (Q.horizontalSection_ae i hy) (k+1)]

lemma normalized_covariant_square (Q : AngularComponentData E r L)
    (hY : IsOpen Y) {K : ℝ} (h : Elliptic Y K g) (hK : 0 < K)
    (he : ∀ i,ContDiffOn ℝ ∞ (fun x => e x i) Y)
    (hframe : ∀ y ∈ Y,∀ i j,metricPair g y (e y i) (e y j) = if i = j then 1 else 0)
    (hφ : smoothNear φ (bundle Y g)) (k : ℕ) (i : I) {y : X} (hy : y ∈ Y) :
    normalizedFischerSquare (k+1) (covariantPolynomialDerivative g e (E.basis k) (Q.coordinates k) y (e y i)) =
      ‖harmonicProjection (k+1) (Q.horizontalSection i y)‖^2 := by
  have hq : covariantPolynomialDerivative g e (E.basis k) (Q.coordinates k) y (e y i) ∈ harmonicHomogeneous (k+1) :=
    ⟨covariantPolynomialDerivative_homogeneous (by omega) g e (E.basis k) (fun j => (E.basisHarmonic k j).1) _ y _,
      covariantPolynomialDerivative_harmonic g e (E.basis k) (fun j => (E.basisHarmonic k j).2) _ y _
        (frameConnection_skew hY h hK e he hframe hy (e y i))⟩
  exact normalizedFischerSquare_eq_projection_norm (k+1) _ hq _ (Q.covariant_polynomial_L2 hY h hK he hframe hφ k i hy)

end AngularComponentData

namespace HarmonicTestExpansion
variable {Y : Set X} {g : MetricField} {e : Frame} {φ : Field}

lemma normalized_real_square (E : HarmonicTestExpansion Y g e φ) (k : ℕ) (y : X) :
    normalizedFischerSquare (k+1) (finitePolynomialField (E.basis k) (E.realCoefficients k) y) =
      ‖harmonicProjection (k+1) (E.realSection y)‖^2 :=
  normalizedFischerSquare_eq_projection_norm (k+1) _
    (finitePolynomialField_harmonicHomogeneous _ _ (E.basisHarmonic k) _ y) _ (E.realCoordinates k y)

lemma normalized_imag_square (E : HarmonicTestExpansion Y g e φ) (k : ℕ) (y : X) :
    normalizedFischerSquare (k+1) (finitePolynomialField (E.basis k) (E.imagCoefficients k) y) =
      ‖harmonicProjection (k+1) (E.imagSection y)‖^2 :=
  normalizedFischerSquare_eq_projection_norm (k+1) _
    (finitePolynomialField_harmonicHomogeneous _ _ (E.basisHarmonic k) _ y) _ (E.imagCoordinates k y)

end HarmonicTestExpansion
end ShrinkingSpheres
