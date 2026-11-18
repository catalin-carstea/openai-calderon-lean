import Proof.SpectralPartialEnergy
import Proof.EnergyPositivity

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open Set MeasureTheory Filter
open scoped ContDiff Topology
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.SphereHarmonic
open OAI.AnisotropicCalderon.SpectralWeightedGraph
open OAI.AnisotropicCalderon.SmoothAngularApplication
open OAI.AnisotropicCalderon.BoundedAngularShift

namespace HarmonicTestExpansion
variable {Y : Set X} {g : MetricField} {e : Frame} {φ : Field}

def realBessel (E : HarmonicTestExpansion Y g e φ) (s : ℝ) (hs : s ≤ 2) : X → SphereL2 :=
  ambientBesselField orthogonalSphereHarmonics denseSphereHarmonics s hs
    (fun p => (E.representative p).re) (Complex.reCLM.contDiff.comp E.representativeSmooth)

def imagBessel (E : HarmonicTestExpansion Y g e φ) (s : ℝ) (hs : s ≤ 2) : X → SphereL2 :=
  ambientBesselField orthogonalSphereHarmonics denseSphereHarmonics s hs
    (fun p => (E.representative p).im) (Complex.imCLM.contDiff.comp E.representativeSmooth)

lemma real_besselGraph (E : HarmonicTestExpansion Y g e φ) (s : ℝ) (hs : s ≤ 2) (y : X) :
    (E.realSection y,E.realBessel s hs y) ∈ sphereBesselGraph orthogonalSphereHarmonics denseSphereHarmonics s :=
  ambientBesselField_graph _ _ s hs _ _ y

lemma imag_besselGraph (E : HarmonicTestExpansion Y g e φ) (s : ℝ) (hs : s ≤ 2) (y : X) :
    (E.imagSection y,E.imagBessel s hs y) ∈ sphereBesselGraph orthogonalSphereHarmonics denseSphereHarmonics s :=
  ambientBesselField_graph _ _ s hs _ _ y

lemma sobolev_eq_besselSquare (E : HarmonicTestExpansion Y g e φ)
    (hframe : ∀ y ∈ Y,∀ i j,metricPair g y (e y i) (e y j) = if i = j then 1 else 0)
    (s : ℝ) (hs : s ≤ 2) {y : X} (hy : y ∈ Y) :
    sobolevSq g e s y (fun w => φ (y,w)) = ‖E.realBessel s hs y‖^2+‖E.imagBessel s hs y‖^2 :=
  sobolevSq_eq_bessel_components g e y (hframe y hy) _ _ _ _ _ (E.realSection_ae hy) (E.imagSection_ae hy) s
    (E.real_besselGraph s hs y) (E.imag_besselGraph s hs y)

lemma partial_sobolev_le (E : HarmonicTestExpansion Y g e φ)
    (hframe : ∀ y ∈ Y,∀ i j,metricPair g y (e y i) (e y j) = if i = j then 1 else 0)
    (s : ℝ) (hs : s ≤ 2) (n : ℕ) {y : X} (hy : y ∈ Y) :
    sobolevSq g e s y (fun w => E.partialField n (y,w)) ≤ sobolevSq g e s y (fun w => φ (y,w)) := by
  rw [E.partial_sobolevSquare hframe s n hy,E.sobolev_eq_besselSquare hframe s hs hy]
  exact partialSobolevSquare_le s n _ _ _ _ (E.real_besselGraph s hs y) (E.imag_besselGraph s hs y)
    (E.zeroDegreeReal y) (E.zeroDegreeImag y)

lemma tendsto_partial_sobolev (E : HarmonicTestExpansion Y g e φ)
    (hframe : ∀ y ∈ Y,∀ i j,metricPair g y (e y i) (e y j) = if i = j then 1 else 0)
    (s : ℝ) (hs : s ≤ 2) {y : X} (hy : y ∈ Y) :
    Tendsto (fun n => sobolevSq g e s y (fun w => E.partialField n (y,w))) atTop
      (𝓝 (sobolevSq g e s y (fun w => φ (y,w)))) := by
  simp_rw [E.partial_sobolevSquare hframe s _ hy]
  rw [E.sobolev_eq_besselSquare hframe s hs hy]
  exact tendsto_partialSobolevSquare s _ _ _ _ (E.real_besselGraph s hs y) (E.imag_besselGraph s hs y)
    (E.zeroDegreeReal y) (E.zeroDegreeImag y)

end HarmonicTestExpansion

namespace AngularComponentData
variable {Y : Set X} {g : MetricField} {e : Frame} {φ : Field} {E : HarmonicTestExpansion Y g e φ}
  {r : X → ℝ} {L : ℂ →L[ℝ] ℝ}

def horizontalBessel (Q : AngularComponentData E r L) (i : I) (s : ℝ) (hs : s ≤ 2) : X → SphereL2 :=
  ambientBesselField orthogonalSphereHarmonics denseSphereHarmonics s hs (Q.horizontalRepresentative i) (Q.horizontalSmooth i)

lemma horizontal_besselGraph (Q : AngularComponentData E r L) (i : I) (s : ℝ) (hs : s ≤ 2) (y : X) :
    (Q.horizontalSection i y,Q.horizontalBessel i s hs y) ∈ sphereBesselGraph orthogonalSphereHarmonics denseSphereHarmonics s :=
  ambientBesselField_graph _ _ s hs _ _ y

end AngularComponentData

namespace AngularModelData
variable {Y : Set X} {g : MetricField} {e : Frame} {φ : Field} {E : HarmonicTestExpansion Y g e φ} {r : X → ℝ}

lemma horizontal_fiber_eq (D : AngularModelData E r) (i : I) {y : X} (hy : y ∈ Y) :
    fiberSq e y (fun w => horizontal g φ y w (e y i)) =
      ‖D.realComponent.horizontalSection i y‖^2+‖D.imagComponent.horizontalSection i y‖^2 :=
  fiberSq_eq_component_norms e y _ _ _ (D.realComponent.horizontalSection_ae i hy) (D.imagComponent.horizontalSection_ae i hy)

lemma horizontal_sobolev_eq (D : AngularModelData E r)
    (hframe : ∀ y ∈ Y,∀ i j,metricPair g y (e y i) (e y j) = if i = j then 1 else 0)
    (i : I) (s : ℝ) (hs : s ≤ 2) {y : X} (hy : y ∈ Y) :
    sobolevSq g e s y (fun w => horizontal g φ y w (e y i)) =
      ‖D.realComponent.horizontalBessel i s hs y‖^2+‖D.imagComponent.horizontalBessel i s hs y‖^2 :=
  sobolevSq_eq_bessel_components g e y (hframe y hy) _ _ _ _ _
    (D.realComponent.horizontalSection_ae i hy) (D.imagComponent.horizontalSection_ae i hy) s
    (D.realComponent.horizontal_besselGraph i s hs y) (D.imagComponent.horizontal_besselGraph i s hs y)

lemma partial_horizontal_fiber_le (D : AngularModelData E r)
    (hY : IsOpen Y) {K : ℝ} (h : Elliptic Y K g) (hK : 0 < K)
    (he : ∀ i,ContDiffOn ℝ ∞ (fun x => e x i) Y)
    (hframe : ∀ y ∈ Y,∀ i j,metricPair g y (e y i) (e y j) = if i = j then 1 else 0)
    (hφ : smoothNear φ (bundle Y g)) (n : ℕ) (i : I) {y : X} (hy : y ∈ Y) :
    fiberSq e y (fun w => horizontal g (E.partialField n) y w (e y i)) ≤
      fiberSq e y (fun w => horizontal g φ y w (e y i)) := by
  rw [D.partial_horizontal_fiberSquare hY h hK he hframe hφ n i hy,D.horizontal_fiber_eq i hy]
  exact partialSobolevSquare_le 0 n _ _ _ _ (sphereBesselGraph_zero_order _ _ _) (sphereBesselGraph_zero_order _ _ _)
    (D.realComponent.horizontalSection_zeroDegree hY h hK he hframe hφ i hy)
    (D.imagComponent.horizontalSection_zeroDegree hY h hK he hframe hφ i hy)

lemma tendsto_partial_horizontal_fiber (D : AngularModelData E r)
    (hY : IsOpen Y) {K : ℝ} (h : Elliptic Y K g) (hK : 0 < K)
    (he : ∀ i,ContDiffOn ℝ ∞ (fun x => e x i) Y)
    (hframe : ∀ y ∈ Y,∀ i j,metricPair g y (e y i) (e y j) = if i = j then 1 else 0)
    (hφ : smoothNear φ (bundle Y g)) (i : I) {y : X} (hy : y ∈ Y) :
    Tendsto (fun n => fiberSq e y (fun w => horizontal g (E.partialField n) y w (e y i))) atTop
      (𝓝 (fiberSq e y (fun w => horizontal g φ y w (e y i)))) := by
  simp_rw [D.partial_horizontal_fiberSquare hY h hK he hframe hφ _ i hy]
  rw [D.horizontal_fiber_eq i hy]
  exact tendsto_partialSobolevSquare 0 _ _ _ _ (sphereBesselGraph_zero_order _ _ _) (sphereBesselGraph_zero_order _ _ _)
    (D.realComponent.horizontalSection_zeroDegree hY h hK he hframe hφ i hy)
    (D.imagComponent.horizontalSection_zeroDegree hY h hK he hframe hφ i hy)

lemma partial_horizontal_sobolev_le (D : AngularModelData E r)
    (hY : IsOpen Y) {K : ℝ} (h : Elliptic Y K g) (hK : 0 < K)
    (he : ∀ i,ContDiffOn ℝ ∞ (fun x => e x i) Y)
    (hframe : ∀ y ∈ Y,∀ i j,metricPair g y (e y i) (e y j) = if i = j then 1 else 0)
    (hφ : smoothNear φ (bundle Y g)) (s : ℝ) (hs : s ≤ 2) (n : ℕ) (i : I) {y : X} (hy : y ∈ Y) :
    sobolevSq g e s y (fun w => horizontal g (E.partialField n) y w (e y i)) ≤
      sobolevSq g e s y (fun w => horizontal g φ y w (e y i)) := by
  rw [D.partial_horizontal_sobolevSquare hY h hK he hframe hφ s n i hy,D.horizontal_sobolev_eq hframe i s hs hy]
  exact partialSobolevSquare_le s n _ _ _ _ (D.realComponent.horizontal_besselGraph i s hs y) (D.imagComponent.horizontal_besselGraph i s hs y)
    (D.realComponent.horizontalSection_zeroDegree hY h hK he hframe hφ i hy)
    (D.imagComponent.horizontalSection_zeroDegree hY h hK he hframe hφ i hy)

lemma tendsto_partial_horizontal_sobolev (D : AngularModelData E r)
    (hY : IsOpen Y) {K : ℝ} (h : Elliptic Y K g) (hK : 0 < K)
    (he : ∀ i,ContDiffOn ℝ ∞ (fun x => e x i) Y)
    (hframe : ∀ y ∈ Y,∀ i j,metricPair g y (e y i) (e y j) = if i = j then 1 else 0)
    (hφ : smoothNear φ (bundle Y g)) (s : ℝ) (hs : s ≤ 2) (i : I) {y : X} (hy : y ∈ Y) :
    Tendsto (fun n => sobolevSq g e s y (fun w => horizontal g (E.partialField n) y w (e y i))) atTop
      (𝓝 (sobolevSq g e s y (fun w => horizontal g φ y w (e y i)))) := by
  simp_rw [D.partial_horizontal_sobolevSquare hY h hK he hframe hφ s _ i hy]
  rw [D.horizontal_sobolev_eq hframe i s hs hy]
  exact tendsto_partialSobolevSquare s _ _ _ _ (D.realComponent.horizontal_besselGraph i s hs y) (D.imagComponent.horizontal_besselGraph i s hs y)
    (D.realComponent.horizontalSection_zeroDegree hY h hK he hframe hφ i hy)
    (D.imagComponent.horizontalSection_zeroDegree hY h hK he hframe hφ i hy)

end AngularModelData
end ShrinkingSpheres
