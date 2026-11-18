import Proof.HarmonicTestExpansion
import Proof.Archive.BoundedAngularShift
import Proof.Archive.SmoothAngularApplication

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open Set MeasureTheory
open scoped ContDiff
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.SphereHarmonic
open OAI.AnisotropicCalderon.SpectralWeightedGraph
open OAI.AnisotropicCalderon.SmoothSphereFields
open OAI.AnisotropicCalderon.SmoothAngularApplication

lemma sphereBesselGraph_one_of_one_two (u u₁ u₂ : SphereL2)
    (h₁ : (u,u₁) ∈ sphereBesselGraph orthogonalSphereHarmonics denseSphereHarmonics 1)
    (h₂ : (u,u₂) ∈ sphereBesselGraph orthogonalSphereHarmonics denseSphereHarmonics 2) :
    (u₁,u₂) ∈ sphereBesselGraph orthogonalSphereHarmonics denseSphereHarmonics 1 := by
  intro k
  rw [h₂ k,h₁ k]
  simp only [besselWeight,Real.rpow_one,Real.rpow_two,smul_smul,pow_two]

def ambientDegreeField (G : X × X → ℝ) (hG : ContDiff ℝ ∞ G) : X → SphereL2 := fun y =>
  ambientBesselField orthogonalSphereHarmonics denseSphereHarmonics 1 (by norm_num) G hG y-ambientSphereL2 G hG y

def ambientDegreeBesselField (G : X × X → ℝ) (hG : ContDiff ℝ ∞ G) : X → SphereL2 := fun y =>
  ambientBesselField orthogonalSphereHarmonics denseSphereHarmonics 2 (by norm_num) G hG y-
    ambientBesselField orthogonalSphereHarmonics denseSphereHarmonics 1 (by norm_num) G hG y

lemma ambientDegree_besselGraph (G : X × X → ℝ) (hG : ContDiff ℝ ∞ G) (y : X) :
    (ambientDegreeField G hG y,ambientDegreeBesselField G hG y) ∈
      sphereBesselGraph orthogonalSphereHarmonics denseSphereHarmonics 1 := by
  have h₁ := ambientBesselField_graph orthogonalSphereHarmonics denseSphereHarmonics 1 (by norm_num) G hG y
  have h₂ := ambientBesselField_graph orthogonalSphereHarmonics denseSphereHarmonics 2 (by norm_num) G hG y
  exact (sphereBesselGraph orthogonalSphereHarmonics denseSphereHarmonics 1).sub_mem
    (sphereBesselGraph_one_of_one_two _ _ _ h₁ h₂) h₁

lemma harmonicProjection_ambientDegree (G : X × X → ℝ) (hG : ContDiff ℝ ∞ G) (y : X) (k : ℕ) :
    harmonicProjection k (ambientDegreeField G hG y) = (k:ℝ) • harmonicProjection k (ambientSphereL2 G hG y) := by
  have hh := ambientBesselField_graph orthogonalSphereHarmonics denseSphereHarmonics 1 (by norm_num) G hG y k
  change harmonicProjection k (ambientBesselField orthogonalSphereHarmonics denseSphereHarmonics 1 (by norm_num) G hG y) =
    besselWeight 1 k • harmonicProjection k (ambientSphereL2 G hG y) at hh
  rw [ambientDegreeField,map_sub,hh]
  simp only [besselWeight,Real.rpow_one,add_smul,one_smul]
  abel

lemma contDiff_ambientDegreeField (G : X × X → ℝ) (hG : ContDiff ℝ ∞ G) : ContDiff ℝ ∞ (ambientDegreeField G hG) :=
  (contDiff_ambientBesselField _ _ 1 (by norm_num) G hG).sub (contDiff_ambientSphereL2 G hG)

lemma contDiff_ambientDegreeBesselField (G : X × X → ℝ) (hG : ContDiff ℝ ∞ G) : ContDiff ℝ ∞ (ambientDegreeBesselField G hG) :=
  (contDiff_ambientBesselField _ _ 2 (by norm_num) G hG).sub (contDiff_ambientBesselField _ _ 1 (by norm_num) G hG)

lemma ambientDegreeField_zero (G : X × X → ℝ) (hG : ContDiff ℝ ∞ G) (S : Set X)
    (hz : ∀ y ∉ S,∀ v : UnitSphere,G (y,v.val) = 0) {y : X} (hy : y ∉ S) : ambientDegreeField G hG y = 0 := by
  rw [ambientDegreeField,ambientBesselField_eq_zero _ _ _ _ G hG S hz y hy,
    ambientSphereL2_eq_zero G hG y (hz y hy),sub_self]

lemma ambientDegreeBesselField_zero (G : X × X → ℝ) (hG : ContDiff ℝ ∞ G) (S : Set X)
    (hz : ∀ y ∉ S,∀ v : UnitSphere,G (y,v.val) = 0) {y : X} (hy : y ∉ S) : ambientDegreeBesselField G hG y = 0 := by
  rw [ambientDegreeBesselField,ambientBesselField_eq_zero _ _ _ _ G hG S hz y hy,
    ambientBesselField_eq_zero _ _ _ _ G hG S hz y hy,sub_self]

end ShrinkingSpheres
