import Proof.AmbientCovariantCoordinates

noncomputable section
set_option autoImplicit false
open Set MeasureTheory Filter
open scoped ContDiff
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.SphereHarmonic
open OAI.AnisotropicCalderon.SmoothSphereFields
open OAI.AnisotropicCalderon.SmoothSphereRotationProjection
open OAI.AnisotropicCalderon.SpectralCoreRegularity
open OAI.AnisotropicCalderon.CovariantHarmonicEnergy

lemma smoothNear.clm_comp {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (L : E →L[ℝ] F) {u : X × X → E}
    {S : Set (X × X)} (hu : smoothNear u S) : smoothNear (fun p => L (u p)) S := by
  obtain ⟨V,hV,hSV,huV⟩ := hu
  exact ⟨V,hV,hSV,L.contDiff.comp_contDiffOn huV⟩

lemma horizontal_clm {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (L : E →L[ℝ] F) (g : MetricField)
    (u : X × X → E) (y w a : X) (hu : DifferentiableAt ℝ u (y,w)) :
    horizontal g (fun p => L (u p)) y w a = L (horizontal g u y w a) := by
  have hh := L.hasFDerivAt.comp (y,w) hu.hasFDerivAt
  change HasFDerivAt (fun p => L (u p)) _ (y,w) at hh
  rw [horizontal,hh.fderiv]
  rfl

/-- Projection of any real linear component of the physical complex horizontal derivative
    is the covariant harmonic derivative of that component's smooth representative. -/
theorem harmonicProjection_horizontal_component {Y : Set X} (hY : IsOpen Y) {K : ℝ} {g : MetricField}
    (h : Elliptic Y K g) (hK : 0 < K) (e : Frame)
    (he : ∀ i,ContDiffOn ℝ ∞ (fun x => e x i) Y)
    (hframe : ∀ y ∈ Y,∀ i j,metricPair g y (e y i) (e y j) = if i = j then 1 else 0)
    (φ : Field) (hφ : smoothNear φ (bundle Y g)) (G : X × X → ℂ) (hG : ContDiff ℝ ∞ G)
    (hrep : ∀ y ∈ Y,∀ v : UnitSphere,G (y,v.val) = φ (y,frameVector e y v.val))
    (L : ℂ →L[ℝ] ℝ) {y : X} (hy : y ∈ Y) (a : X) (H : SphereL2)
    (hH : H =ᵐ[sphereProbability] (fun v : UnitSphere => L (horizontal g φ y (frameVector e y v.val) a))) (k : ℕ) :
    harmonicProjection k H = harmonicCovariantDerivative g e k
      (fun y => harmonicProjection k (ambientSphereL2 (fun p => L (G p)) (L.contDiff.comp hG) y)) y a := by
  apply harmonicProjection_horizontal hY h hK e he hframe (fun p => L (φ p))
    (hφ.clm_comp L) (fun p => L (G p)) (L.contDiff.comp hG)
    (fun x hx v => congrArg L (hrep x hx v)) hy a H
  apply hH.trans
  apply Filter.Eventually.of_forall
  intro v
  exact (horizontal_clm L g φ y (frameVector e y v.val) a
    (hφ.differentiableAt ⟨hy,frameVector_mem_sphere g e y (hframe y hy) v⟩)).symm

end ShrinkingSpheres
