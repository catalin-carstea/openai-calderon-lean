import Proof.DegreeBesselFields
import Proof.BesselTruncationConvergence

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
open OAI.AnisotropicCalderon.AngularShiftGraph
open OAI.AnisotropicCalderon.BoundedAngularShift

/-- The signed weighted horizontal field, with the degree acting on the original test. -/
def weightedAngularSection (H G : X × X → ℝ) (hH : ContDiff ℝ ∞ H) (hG : ContDiff ℝ ∞ G)
    (b : X → ℝ) (s : ℝ) : X → SphereL2 := fun y =>
  s • ambientSphereL2 H hH y+b y • ambientDegreeField G hG y

def weightedAngularBesselSection (H G : X × X → ℝ) (hH : ContDiff ℝ ∞ H) (hG : ContDiff ℝ ∞ G)
    (b : X → ℝ) (s : ℝ) : X → SphereL2 := fun y =>
  s • ambientBesselField orthogonalSphereHarmonics denseSphereHarmonics 1 (by norm_num) H hH y+
    b y • ambientDegreeBesselField G hG y

lemma weightedAngularSection_besselGraph (H G : X × X → ℝ) (hH : ContDiff ℝ ∞ H) (hG : ContDiff ℝ ∞ G)
    (b : X → ℝ) (s : ℝ) (y : X) :
    (weightedAngularSection H G hH hG b s y,weightedAngularBesselSection H G hH hG b s y) ∈
      sphereBesselGraph orthogonalSphereHarmonics denseSphereHarmonics 1 := by
  intro k
  change harmonicProjection k (s • ambientBesselField orthogonalSphereHarmonics denseSphereHarmonics 1 (by norm_num) H hH y+
      b y • ambientDegreeBesselField G hG y) =
    besselWeight 1 k • harmonicProjection k (s • ambientSphereL2 H hH y+b y • ambientDegreeField G hG y)
  have h₁ := ambientBesselField_graph orthogonalSphereHarmonics denseSphereHarmonics 1 (by norm_num) H hH y k
  have h₂ := ambientDegree_besselGraph G hG y k
  change harmonicProjection k (ambientBesselField orthogonalSphereHarmonics denseSphereHarmonics 1 (by norm_num) H hH y) =
    besselWeight 1 k • harmonicProjection k (ambientSphereL2 H hH y) at h₁
  change harmonicProjection k (ambientDegreeBesselField G hG y) =
    besselWeight 1 k • harmonicProjection k (ambientDegreeField G hG y) at h₂
  rw [map_add,map_smul,map_smul,map_add,map_smul,map_smul,h₁,h₂,smul_add]
  simp only [smul_smul,mul_comm]

lemma contDiff_weightedAngularBesselSection (H G : X × X → ℝ) (hH : ContDiff ℝ ∞ H) (hG : ContDiff ℝ ∞ G)
    (b : X → ℝ) (hb : ContDiff ℝ ∞ b) (s : ℝ) :
    ContDiff ℝ ∞ (weightedAngularBesselSection H G hH hG b s) :=
  ((contDiff_ambientBesselField _ _ 1 (by norm_num) H hH).const_smul s).add
    (hb.smul (contDiff_ambientDegreeBesselField G hG))

lemma weightedAngularBesselSection_zero (H G : X × X → ℝ) (hH : ContDiff ℝ ∞ H) (hG : ContDiff ℝ ∞ G)
    (b : X → ℝ) (s : ℝ) (S : Set X)
    (hHz : ∀ y ∉ S,∀ v : UnitSphere,H (y,v.val) = 0)
    (hGz : ∀ y ∉ S,∀ v : UnitSphere,G (y,v.val) = 0) {y : X} (hy : y ∉ S) :
    weightedAngularBesselSection H G hH hG b s y = 0 := by
  rw [weightedAngularBesselSection,ambientBesselField_eq_zero _ _ _ _ H hH S hHz y hy,
    ambientDegreeBesselField_zero G hG S hGz hy,smul_zero,smul_zero,add_zero]

def angularRaisingSection (i : I) (H G : X × X → ℝ) (hH : ContDiff ℝ ∞ H) (hG : ContDiff ℝ ∞ G)
    (b : X → ℝ) : X → SphereL2 := fun y =>
  normalizedRaising sphereFischerInner orthogonalSphereHarmonics denseSphereHarmonics i
    (weightedAngularBesselSection H G hH hG b 1 y)

def angularLoweringSection (i : I) (H G : X × X → ℝ) (hH : ContDiff ℝ ∞ H) (hG : ContDiff ℝ ∞ G)
    (b : X → ℝ) : X → SphereL2 := fun y =>
  normalizedDerivative sphereFischerInner orthogonalSphereHarmonics denseSphereHarmonics i
    (weightedAngularBesselSection H G hH hG b (-1) y)

lemma angularRaisingSection_graph (i : I) (H G : X × X → ℝ) (hH : ContDiff ℝ ∞ H) (hG : ContDiff ℝ ∞ G)
    (b : X → ℝ) (y : X) :
    (weightedAngularSection H G hH hG b 1 y,angularRaisingSection i H G hH hG b y) ∈
      sphereRaisingGraph sphereFischerInner orthogonalSphereHarmonics denseSphereHarmonics i :=
  normalizedRaising_graph _ _ _ i _ _ (weightedAngularSection_besselGraph H G hH hG b 1 y)

lemma angularLoweringSection_graph (i : I) (H G : X × X → ℝ) (hH : ContDiff ℝ ∞ H) (hG : ContDiff ℝ ∞ G)
    (b : X → ℝ) (y : X) :
    (weightedAngularSection H G hH hG b (-1) y,angularLoweringSection i H G hH hG b y) ∈
      sphereDerivativeGraph sphereFischerInner orthogonalSphereHarmonics denseSphereHarmonics i :=
  normalizedDerivative_graph _ _ _ i _ _ (weightedAngularSection_besselGraph H G hH hG b (-1) y)

lemma contDiff_angularRaisingSection (i : I) (H G : X × X → ℝ) (hH : ContDiff ℝ ∞ H) (hG : ContDiff ℝ ∞ G)
    (b : X → ℝ) (hb : ContDiff ℝ ∞ b) : ContDiff ℝ ∞ (angularRaisingSection i H G hH hG b) :=
  (normalizedRaising sphereFischerInner orthogonalSphereHarmonics denseSphereHarmonics i).contDiff.comp
    (contDiff_weightedAngularBesselSection H G hH hG b hb 1)

lemma contDiff_angularLoweringSection (i : I) (H G : X × X → ℝ) (hH : ContDiff ℝ ∞ H) (hG : ContDiff ℝ ∞ G)
    (b : X → ℝ) (hb : ContDiff ℝ ∞ b) : ContDiff ℝ ∞ (angularLoweringSection i H G hH hG b) :=
  (normalizedDerivative sphereFischerInner orthogonalSphereHarmonics denseSphereHarmonics i).contDiff.comp
    (contDiff_weightedAngularBesselSection H G hH hG b hb (-1))

lemma angularRaisingSection_zero (i : I) (H G : X × X → ℝ) (hH : ContDiff ℝ ∞ H) (hG : ContDiff ℝ ∞ G)
    (b : X → ℝ) (S : Set X) (hHz : ∀ y ∉ S,∀ v : UnitSphere,H (y,v.val) = 0)
    (hGz : ∀ y ∉ S,∀ v : UnitSphere,G (y,v.val) = 0) {y : X} (hy : y ∉ S) :
    angularRaisingSection i H G hH hG b y = 0 := by
  rw [angularRaisingSection,weightedAngularBesselSection_zero H G hH hG b 1 S hHz hGz hy,map_zero]

lemma angularLoweringSection_zero (i : I) (H G : X × X → ℝ) (hH : ContDiff ℝ ∞ H) (hG : ContDiff ℝ ∞ G)
    (b : X → ℝ) (S : Set X) (hHz : ∀ y ∉ S,∀ v : UnitSphere,H (y,v.val) = 0)
    (hGz : ∀ y ∉ S,∀ v : UnitSphere,G (y,v.val) = 0) {y : X} (hy : y ∉ S) :
    angularLoweringSection i H G hH hG b y = 0 := by
  rw [angularLoweringSection,weightedAngularBesselSection_zero H G hH hG b (-1) S hHz hGz hy,map_zero]

end ShrinkingSpheres
