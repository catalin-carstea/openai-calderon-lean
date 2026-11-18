import Proof.CanonicalSmoothSobolevSection
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxSynthPendingDepth 25
set_option maxRecDepth 2400
open Set
open scoped ContDiff Topology
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.SphereHarmonic OAI.AnisotropicCalderon.SpectralWeightedGraph
open OAI.AnisotropicCalderon.SpectralCoreRegularity OAI.AnisotropicCalderon.SmoothSphereFields
open OAI.AnisotropicCalderon.SmoothAmbientAngularCasimir
open OAI.AnisotropicCalderon.SmoothAngularApplication OAI.AnisotropicCalderon.BoundedSpectralMultiplier
open OAI.AnisotropicCalderon.SpectralWeightComparison

/-- Two genuine Casimir inversions lift a smooth sphere family through
angular order four. This is a qualitative domain construction, not a new
uniform derivative bound on the small tensor. -/
def ambientHigherBesselField (s : ℝ) (hs : s ≤ 4) (G : X × X → ℝ) (hG : ContDiff ℝ ∞ G) : X → SphereL2 :=
  fun y => casimirBesselMultiplier orthogonalSphereHarmonics denseSphereHarmonics (s/2) (by linarith)
    (casimirBesselMultiplier orthogonalSphereHarmonics denseSphereHarmonics (s/2) (by linarith)
      (ambientSphereL2 (ambientShiftedAngularCasimirIterate 2 G)
        (contDiff_ambientShiftedAngularCasimirIterate 2 G hG) y))

lemma ambientHigherBesselField_graph (s : ℝ) (hs : s ≤ 4) (G : X × X → ℝ) (hG : ContDiff ℝ ∞ G) (y : X) :
    (ambientSphereL2 G hG y,ambientHigherBesselField s hs G hG y) ∈
      sphereBesselGraph orthogonalSphereHarmonics denseSphereHarmonics s := by
  let C := casimirBesselMultiplier orthogonalSphereHarmonics denseSphereHarmonics (s/2) (by linarith : s/2 ≤ 2)
  let U := ambientSphereL2 (ambientShiftedAngularCasimirIterate 2 G)
    (contDiff_ambientShiftedAngularCasimirIterate 2 G hG) y
  have hC (v : SphereL2) := boundedSpectralMultiplier_mem orthogonalSphereHarmonics denseSphereHarmonics
    (casimirBesselRatio (s/2)) 2 (by norm_num) (abs_casimirBesselRatio_le_two (s/2) (by linarith)) v
  intro k
  have hBase := sphereHarmonicCoordinate_angularCasimirLift orthogonalSphereHarmonics denseSphereHarmonics 2 k G hG y
  have hw : besselWeight (s/2) k*besselWeight (s/2) k=besselWeight s k := by
    dsimp only [besselWeight]
    rw [←Real.rpow_add (by positivity : 0 < 1+(k:ℝ))]
    congr 1
    ring
  have hRatio : casimirBesselRatio (s/2) k*casimirBesselRatio (s/2) k*(casimirWeight k)^2=besselWeight s k := by
    rw [←pow_two,casimirBesselRatio,div_pow,div_mul_cancel₀ _ (pow_ne_zero 2 (casimirWeight_pos k).ne'),pow_two,hw]
  change sphereHarmonicCoordinate orthogonalSphereHarmonics denseSphereHarmonics k (C (C U))=_
  have hCv (v : SphereL2) : sphereHarmonicCoordinate orthogonalSphereHarmonics denseSphereHarmonics k (C v)=
      casimirBesselRatio (s/2) k • sphereHarmonicCoordinate orthogonalSphereHarmonics denseSphereHarmonics k v := hC v k
  rw [hCv (C U),hCv U,hBase,smul_smul,smul_smul]
  change (casimirBesselRatio (s/2) k*casimirBesselRatio (s/2) k*(casimirWeight k)^2) •
    sphereHarmonicCoordinate orthogonalSphereHarmonics denseSphereHarmonics k (ambientSphereL2 G hG y)=
    besselWeight s k • sphereHarmonicCoordinate orthogonalSphereHarmonics denseSphereHarmonics k (ambientSphereL2 G hG y)
  rw [hRatio]

lemma contDiff_ambientHigherBesselField (s : ℝ) (hs : s ≤ 4) (G : X × X → ℝ) (hG : ContDiff ℝ ∞ G) :
    ContDiff ℝ ∞ (ambientHigherBesselField s hs G hG) :=
  (casimirBesselMultiplier orthogonalSphereHarmonics denseSphereHarmonics (s/2) (by linarith)).contDiff.comp
    ((casimirBesselMultiplier orthogonalSphereHarmonics denseSphereHarmonics (s/2) (by linarith)).contDiff.comp
      (contDiff_angularCasimirLift 2 G hG))

def ambientHigherSobolevSection (s : ℝ) (hs : s ≤ 4) (G : X × X → ℝ) (hG : ContDiff ℝ ∞ G) : X → SphereSobolev s :=
  fun y => sphereSobolevBesselOrderL 0 s
    (sphereSobolevZeroEquiv orthogonalSphereHarmonics denseSphereHarmonics (ambientHigherBesselField s hs G hG y))

lemma ambientHigherSobolevSection_coefficient (s : ℝ) (hs : s ≤ 4)
    (G : X × X → ℝ) (hG : ContDiff ℝ ∞ G) (y : X) (k : ℕ) :
    sphereSobolevCoefficientL s k (ambientHigherSobolevSection s hs G hG y)=
      sphereHarmonicCoordinate orthogonalSphereHarmonics denseSphereHarmonics k (ambientSphereL2 G hG y) := by
  unfold ambientHigherSobolevSection
  rw [sphereSobolevCoefficientL_besselOrder,sphereSobolevCoefficientL_zeroEquiv,
    ambientHigherBesselField_graph s hs G hG y k,smul_smul,zero_sub,besselWeight_neg_mul_self,one_smul]

lemma contDiff_ambientHigherSobolevSection (s : ℝ) (hs : s ≤ 4) (G : X × X → ℝ) (hG : ContDiff ℝ ∞ G) :
    ContDiff ℝ ∞ (ambientHigherSobolevSection s hs G hG) :=
  (sphereSobolevBesselOrderL 0 s).contDiff.comp
    ((sphereSobolevZeroEquiv orthogonalSphereHarmonics denseSphereHarmonics).contDiff.comp
      (contDiff_ambientHigherBesselField s hs G hG))

lemma ambientHigherSobolevSection_inclusion (s t : ℝ) (hs : s ≤ 4) (ht : t ≤ 2) (hst : t ≤ s)
    (G : X × X → ℝ) (hG : ContDiff ℝ ∞ G) (y : X) :
    sphereSobolevInclusionL s t hst (ambientHigherSobolevSection s hs G hG y)=ambientSobolevSection t ht G hG y := by
  apply sphereSobolev_ext t
  intro k
  rw [sphereSobolevCoefficientL_inclusion,ambientHigherSobolevSection_coefficient,ambientSobolevSection_coefficient]
end ShrinkingSpheres
