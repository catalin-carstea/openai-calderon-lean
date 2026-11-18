import Proof.ComplexHilbertProjection
import Proof.Archive.SmoothAngularApplication
import Proof.WeightedHarmonicConvergence

noncomputable section
set_option autoImplicit false
open Set MeasureTheory MvPolynomial Filter
open scoped ContDiff Topology
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.SphereHarmonic
open OAI.AnisotropicCalderon.SpectralWeightedGraph
open OAI.AnisotropicCalderon.SpectralCoreRegularity
open OAI.AnisotropicCalderon.SmoothSphereFields
open OAI.AnisotropicCalderon.SmoothAngularApplication

lemma besselWeight_square (s : ℝ) (k : ℕ) : |besselWeight s k|^2 = (1+(k : ℝ))^(2*s) := by
  rw [abs_of_pos (besselWeight_pos s k),besselWeight,← Real.rpow_two,
    ← Real.rpow_mul (by positivity)]
  congr 1
  ring

lemma summable_bessel_components (s : ℝ) (u b : SphereL2)
    (hb : (u,b) ∈ sphereBesselGraph orthogonalSphereHarmonics denseSphereHarmonics s) :
    Summable (fun k : ℕ => (1+(k : ℝ))^(2*s)*‖harmonicProjection k u‖^2) := by
  have hh := (exists_spectralGraph_iff_summable orthogonalSphereHarmonics denseSphereHarmonics
    (besselWeight s) u).mp ⟨b,hb⟩
  simpa only [besselWeight_square,harmonicProjection] using hh

lemma norm_sq_bessel_components (s : ℝ) (u b : SphereL2)
    (hb : (u,b) ∈ sphereBesselGraph orthogonalSphereHarmonics denseSphereHarmonics s) :
    ‖b‖^2 = ∑' k : ℕ,(1+(k : ℝ))^(2*s)*‖harmonicProjection k u‖^2 := by
  simpa only [besselWeight_square,harmonicProjection] using
    norm_sq_spectralGraph_output orthogonalSphereHarmonics denseSphereHarmonics (besselWeight s) u b hb

/-- Exact Sobolev square from the two closed Bessel graphs. Their graph membership supplies
    summability before the real and imaginary infinite series are split. -/
theorem sobolevSq_eq_bessel_components (g : MetricField) (e : Frame) (y : X)
    (hframe : ∀ i j,metricPair g y (e y i) (e y j) = if i = j then 1 else 0)
    (F : X → ℂ) (U V B C : SphereL2)
    (hRe : U =ᵐ[sphereProbability] (fun v : UnitSphere => (F (frameVector e y v.val)).re))
    (hIm : V =ᵐ[sphereProbability] (fun v : UnitSphere => (F (frameVector e y v.val)).im))
    (s : ℝ) (hB : (U,B) ∈ sphereBesselGraph orthogonalSphereHarmonics denseSphereHarmonics s)
    (hC : (V,C) ∈ sphereBesselGraph orthogonalSphereHarmonics denseSphereHarmonics s) :
    sobolevSq g e s y F = ‖B‖^2+‖C‖^2 := by
  rw [sobolevSq_harmonicProjection_components g e y hframe F U V hRe hIm]
  simp_rw [mul_add]
  rw [(summable_bessel_components s U B hB).tsum_add (summable_bessel_components s V C hC),
    ← norm_sq_bessel_components s U B hB,← norm_sq_bessel_components s V C hC]

/-- A smooth compact standard-sphere representative gives smooth compact Bessel sections
    through order two, enough for every angular Sobolev order in the frozen energy. -/
theorem exists_smooth_bessel_sections (G : X × X → ℂ) (hG : ContDiff ℝ ∞ G)
    (K : Set X) (hK : IsCompact K) (hzero : ∀ x ∉ K,∀ v : UnitSphere,G (x,v.val) = 0)
    (s : ℝ) (hs : s ≤ 2) :
    ∃ U V B C : X → SphereL2,
      ContDiff ℝ ∞ U ∧ ContDiff ℝ ∞ V ∧ ContDiff ℝ ∞ B ∧ ContDiff ℝ ∞ C ∧
      HasCompactSupport B ∧ HasCompactSupport C ∧
      tsupport B ⊆ K ∧ tsupport C ⊆ K ∧
      (∀ x,U x =ᵐ[sphereProbability] (fun v : UnitSphere => (G (x,v.val)).re)) ∧
      (∀ x,V x =ᵐ[sphereProbability] (fun v : UnitSphere => (G (x,v.val)).im)) ∧
      (∀ x,(U x,B x) ∈ sphereBesselGraph orthogonalSphereHarmonics denseSphereHarmonics s) ∧
      (∀ x,(V x,C x) ∈ sphereBesselGraph orthogonalSphereHarmonics denseSphereHarmonics s) := by
  let Gre : X × X → ℝ := fun z => (G z).re
  let Gim : X × X → ℝ := fun z => (G z).im
  have hGre : ContDiff ℝ ∞ Gre := Complex.reCLM.contDiff.comp hG
  have hGim : ContDiff ℝ ∞ Gim := Complex.imCLM.contDiff.comp hG
  have hzr : ∀ x ∉ K,∀ v : UnitSphere,Gre (x,v.val) = 0 := by
    intro x hx v
    simp only [Gre,hzero x hx v,Complex.zero_re]
  have hzi : ∀ x ∉ K,∀ v : UnitSphere,Gim (x,v.val) = 0 := by
    intro x hx v
    simp only [Gim,hzero x hx v,Complex.zero_im]
  refine ⟨ambientSphereL2 Gre hGre,ambientSphereL2 Gim hGim,
    ambientBesselField orthogonalSphereHarmonics denseSphereHarmonics s hs Gre hGre,
    ambientBesselField orthogonalSphereHarmonics denseSphereHarmonics s hs Gim hGim,
    contDiff_ambientSphereL2 Gre hGre,contDiff_ambientSphereL2 Gim hGim,
    contDiff_ambientBesselField _ _ s hs Gre hGre,contDiff_ambientBesselField _ _ s hs Gim hGim,
    hasCompactSupport_ambientBesselField _ _ s hs Gre hGre K hK hzr,
    hasCompactSupport_ambientBesselField _ _ s hs Gim hGim K hK hzi,
    tsupport_ambientBesselField_subset _ _ s hs Gre hGre K hK hzr,
    tsupport_ambientBesselField_subset _ _ s hs Gim hGim K hK hzi,
    ambientSphereL2_ae Gre hGre,ambientSphereL2_ae Gim hGim,
    ambientBesselField_graph _ _ s hs Gre hGre,ambientBesselField_graph _ _ s hs Gim hGim⟩

/-- Every admitted local test has a continuous compactly supported representative of each
    angular Sobolev square used by the estimate. This is an equality with the frozen kernel. -/
theorem exists_sobolev_square_representative_of_support {Y : Set X} (hY : IsOpen Y) {g : MetricField} (e : Frame)
    (he : ∀ i,ContDiffOn ℝ ∞ (fun x => e x i) Y)
    (hframe : ∀ y ∈ Y,∀ i j,metricPair g y (e y i) (e y j) = if i = j then 1 else 0)
    {φ : Field} (hφ : smoothNear φ (bundle Y g))
    (hcpt : ∃ K,IsCompact K ∧ K ⊆ Y ∧ ∀ y ∈ Y \ K,∀ w ∈ sphereAt g y,φ (y,w) = 0)
    (s : ℝ) (hs : s ≤ 2) :
    ∃ Q : X → ℝ,Continuous Q ∧ HasCompactSupport Q ∧ tsupport Q ⊆ Y ∧
      (∀ y,0 ≤ Q y) ∧ ∀ y ∈ Y,Q y = sobolevSq g e s y (fun w => φ (y,w)) := by
  obtain ⟨K,hK,hKY,G,hG,hrep,hzero⟩ := exists_smooth_standard_representative_of_support hY e he hframe hφ hcpt
  obtain ⟨U,V,B,C,hU,hV,hB,hC,hcompB,hcompC,hsB,hsC,hRe,hIm,hgraphB,hgraphC⟩ :=
    exists_smooth_bessel_sections G hG K hK hzero s hs
  let Q : X → ℝ := fun y => ‖B y‖^2+‖C y‖^2
  have hQ : Continuous Q := (hB.continuous.norm.pow 2).add (hC.continuous.norm.pow 2)
  have hz (y : X) (hy : y ∉ K) : Q y = 0 := by
    have hb : y ∉ tsupport B := fun ht => hy (hsB ht)
    have hc : y ∉ tsupport C := fun ht => hy (hsC ht)
    simp only [Q,image_eq_zero_of_notMem_tsupport hb,image_eq_zero_of_notMem_tsupport hc,norm_zero,
      zero_pow (by omega : 2 ≠ 0),add_zero]
  have hsupp : tsupport Q ⊆ K := by
    apply closure_minimal _ hK.isClosed
    intro y hy
    by_contra hn
    exact hy (hz y hn)
  refine ⟨Q,hQ,HasCompactSupport.intro hK hz,hsupp.trans hKY,fun y => by dsimp [Q]; positivity,?_⟩
  intro y hy
  have hr : U y =ᵐ[sphereProbability] (fun v : UnitSphere => (φ (y,frameVector e y v.val)).re) := by
    apply (hRe y).trans
    exact Filter.Eventually.of_forall (fun v => congrArg Complex.re (hrep y hy v))
  have hi : V y =ᵐ[sphereProbability] (fun v : UnitSphere => (φ (y,frameVector e y v.val)).im) := by
    apply (hIm y).trans
    exact Filter.Eventually.of_forall (fun v => congrArg Complex.im (hrep y hy v))
  exact (sobolevSq_eq_bessel_components g e y (hframe y hy) (fun w => φ (y,w))
    (U y) (V y) (B y) (C y) hr hi s (hgraphB y) (hgraphC y)).symm

theorem Test.exists_sobolev_square_representative {Y : Set X} (hY : IsOpen Y) {g : MetricField} (e : Frame)
    (he : ∀ i,ContDiffOn ℝ ∞ (fun x => e x i) Y)
    (hframe : ∀ y ∈ Y,∀ i j,metricPair g y (e y i) (e y j) = if i = j then 1 else 0)
    {φ : Field} (hφ : Test Y g e φ) (s : ℝ) (hs : s ≤ 2) :
    ∃ Q : X → ℝ,Continuous Q ∧ HasCompactSupport Q ∧ tsupport Q ⊆ Y ∧
      (∀ y,0 ≤ Q y) ∧ ∀ y ∈ Y,Q y = sobolevSq g e s y (fun w => φ (y,w)) :=
  exists_sobolev_square_representative_of_support hY e he hframe hφ.1 hφ.2.1 s hs

lemma sobolevSq_zero_eq_fiberSq_components (g : MetricField) (e : Frame) (y : X)
    (hframe : ∀ i j,metricPair g y (e y i) (e y j) = if i = j then 1 else 0)
    (F : X → ℂ) (U V : SphereL2)
    (hRe : U =ᵐ[sphereProbability] (fun v : UnitSphere => (F (frameVector e y v.val)).re))
    (hIm : V =ᵐ[sphereProbability] (fun v : UnitSphere => (F (frameVector e y v.val)).im)) :
    sobolevSq g e 0 y F = fiberSq e y F := by
  have hgraph (u : SphereL2) : (u,u) ∈ sphereBesselGraph orthogonalSphereHarmonics denseSphereHarmonics 0 := by
    intro k
    rw [besselWeight_zero_order,one_smul]
  rw [sobolevSq_eq_bessel_components g e y hframe F U V U V hRe hIm 0 (hgraph U) (hgraph V),
    fiberSq_eq_component_norms e y F U V hRe hIm]

lemma exists_fiber_square_representative_of_support {Y : Set X} (hY : IsOpen Y) {g : MetricField} (e : Frame)
    (he : ∀ i,ContDiffOn ℝ ∞ (fun x => e x i) Y)
    (hframe : ∀ y ∈ Y,∀ i j,metricPair g y (e y i) (e y j) = if i = j then 1 else 0)
    {φ : Field} (hφ : smoothNear φ (bundle Y g))
    (hcpt : ∃ K,IsCompact K ∧ K ⊆ Y ∧ ∀ y ∈ Y \ K,∀ w ∈ sphereAt g y,φ (y,w) = 0) :
    ∃ Q : X → ℝ,Continuous Q ∧ HasCompactSupport Q ∧ tsupport Q ⊆ Y ∧
      (∀ y,0 ≤ Q y) ∧ ∀ y ∈ Y,Q y = fiberSq e y (fun w => φ (y,w)) := by
  obtain ⟨Q,hQ,hcomp,hsupp,hpos,hEq⟩ :=
    exists_sobolev_square_representative_of_support hY e he hframe hφ hcpt 0 (by norm_num)
  obtain ⟨K,hK,hKY,G,hG,hrep,hzero⟩ :=
    exists_smooth_standard_representative_of_support hY e he hframe hφ hcpt
  obtain ⟨U,V,B,C,hU,hV,hB,hC,hcompB,hcompC,hsB,hsC,hRe,hIm,hgraphB,hgraphC⟩ :=
    exists_smooth_bessel_sections G hG K hK hzero 0 (by norm_num)
  refine ⟨Q,hQ,hcomp,hsupp,hpos,?_⟩
  intro y hy
  rw [hEq y hy]
  apply sobolevSq_zero_eq_fiberSq_components g e y (hframe y hy) (fun w => φ (y,w)) (U y) (V y)
  · apply (hRe y).trans
    exact Filter.Eventually.of_forall (fun v => congrArg Complex.re (hrep y hy v))
  · apply (hIm y).trans
    exact Filter.Eventually.of_forall (fun v => congrArg Complex.im (hrep y hy v))

end ShrinkingSpheres
