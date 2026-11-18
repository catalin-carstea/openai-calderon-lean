import Proof.ComplexBesselSections
import Proof.Archive.SphereSobolevBesselOrderCompatibility
import Proof.Archive.SmoothAngularCoordinates
import Proof.Archive.SphereSobolevOrderOneRotation
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxSynthPendingDepth 25
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
open Set
open scoped ContDiff Topology
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.SphereHarmonic OAI.AnisotropicCalderon.SpectralWeightedGraph
open OAI.AnisotropicCalderon.SpectralCoreRegularity OAI.AnisotropicCalderon.SmoothSphereFields
open OAI.AnisotropicCalderon.SmoothAngularApplication OAI.AnisotropicCalderon.SmoothMovingFrameFields
open OAI.AnisotropicCalderon.SmoothAmbientAngularCasimir

/-- The Bessel section is decoded through the canonical Bessel-order map.
    Its coefficients are those of the original smooth sphere field. -/
def ambientSobolevSection (s : ℝ) (hs : s ≤ 2) (G : X × X → ℝ) (hG : ContDiff ℝ ∞ G) : X → SphereSobolev s :=
  fun y => sphereSobolevBesselOrderL 0 s
    (sphereSobolevZeroEquiv orthogonalSphereHarmonics denseSphereHarmonics
      (ambientBesselField orthogonalSphereHarmonics denseSphereHarmonics s hs G hG y))

lemma contDiff_ambientSobolevSection (s : ℝ) (hs : s ≤ 2) (G : X × X → ℝ) (hG : ContDiff ℝ ∞ G) :
    ContDiff ℝ ∞ (ambientSobolevSection s hs G hG) :=
  (sphereSobolevBesselOrderL 0 s).contDiff.comp
    ((sphereSobolevZeroEquiv orthogonalSphereHarmonics denseSphereHarmonics).contDiff.comp
      (contDiff_ambientBesselField orthogonalSphereHarmonics denseSphereHarmonics s hs G hG))

lemma ambientSobolevSection_coefficient (s : ℝ) (hs : s ≤ 2) (G : X × X → ℝ) (hG : ContDiff ℝ ∞ G)
    (y : X) (k : ℕ) :
    sphereSobolevCoefficientL s k (ambientSobolevSection s hs G hG y)=
      sphereHarmonicCoordinate orthogonalSphereHarmonics denseSphereHarmonics k (ambientSphereL2 G hG y) := by
  unfold ambientSobolevSection
  rw [sphereSobolevCoefficientL_besselOrder,sphereSobolevCoefficientL_zeroEquiv]
  have hGraph := ambientBesselField_graph orthogonalSphereHarmonics denseSphereHarmonics s hs G hG y k
  rw [hGraph,smul_smul,zero_sub,besselWeight_neg_mul_self,one_smul]

lemma ambientSobolevSection_coarse (s : ℝ) (hs : s ≤ 2) (h0 : 0 ≤ s)
    (G : X × X → ℝ) (hG : ContDiff ℝ ∞ G) (y : X) :
    sphereSobolevInclusionL s 0 h0 (ambientSobolevSection s hs G hG y)=
      sphereSobolevZeroEquiv orthogonalSphereHarmonics denseSphereHarmonics (ambientSphereL2 G hG y) := by
  apply sphereSobolev_ext 0
  intro k
  rw [sphereSobolevCoefficientL_inclusion,ambientSobolevSection_coefficient,sphereSobolevCoefficientL_zeroEquiv]

lemma norm_ambientSobolevSection (s : ℝ) (hs : s ≤ 2) (G : X × X → ℝ) (hG : ContDiff ℝ ∞ G) (y : X) :
    ‖ambientSobolevSection s hs G hG y‖=
      ‖ambientBesselField orthogonalSphereHarmonics denseSphereHarmonics s hs G hG y‖ := by
  change ‖sphereSobolevZeroEquiv orthogonalSphereHarmonics denseSphereHarmonics
    (ambientBesselField orthogonalSphereHarmonics denseSphereHarmonics s hs G hG y)‖= _
  exact (sphereSobolevZeroEquiv orthogonalSphereHarmonics denseSphereHarmonics).norm_map _

lemma ambientSobolevSection_inclusion (s t : ℝ) (hs : s ≤ 2) (ht : t ≤ 2) (hst : t ≤ s)
    (G : X × X → ℝ) (hG : ContDiff ℝ ∞ G) (y : X) :
    sphereSobolevInclusionL s t hst (ambientSobolevSection s hs G hG y)=ambientSobolevSection t ht G hG y := by
  apply sphereSobolev_ext t
  intro k
  rw [sphereSobolevCoefficientL_inclusion,ambientSobolevSection_coefficient,ambientSobolevSection_coefficient]

lemma ambientSobolevSection_rotation (i j : I) (G : X × X → ℝ) (hG : ContDiff ℝ ∞ G) (y : X) :
    sphereSobolevRotationL 1 i j (ambientSobolevSection 1 (by norm_num) G hG y)=
      sphereSobolevZeroEquiv orthogonalSphereHarmonics denseSphereHarmonics
        (ambientSphereL2 (ambientAngularRotation i j G) (contDiff_ambientAngularRotation i j G hG) y) := by
  apply sphereSobolev_ext 0
  intro k
  have hCoeff := sphereSobolevCoefficientL_rotation 1 i j k (ambientSobolevSection 1 (by norm_num) G hG y)
  have hCoeff0 : sphereSobolevCoefficientL 0 k (sphereSobolevRotationL 1 i j
      (ambientSobolevSection 1 (by norm_num) G hG y))=
      OAI.AnisotropicCalderon.SmoothSphereRotationProjection.harmonicSphereRotation k i j
        (sphereSobolevCoefficientL 1 k (ambientSobolevSection 1 (by norm_num) G hG y)) := by
    have hOrder : sphereSobolevCoefficientL ((1:ℝ)-1) k
        (sphereSobolevRotationL 1 i j (ambientSobolevSection 1 (by norm_num) G hG y))=
        sphereSobolevCoefficientL 0 k
          (sphereSobolevRotationL 1 i j (ambientSobolevSection 1 (by norm_num) G hG y)) :=
      congrArg (fun t : ℝ => sphereSobolevCoefficientL t k
        (sphereSobolevRotationL 1 i j (ambientSobolevSection 1 (by norm_num) G hG y))) (by norm_num : (1:ℝ)-1=0)
    exact hOrder.symm.trans hCoeff
  rw [hCoeff0,ambientSobolevSection_coefficient,sphereSobolevCoefficientL_zeroEquiv]
  exact (sphereHarmonicCoordinate_ambientAngularRotation orthogonalSphereHarmonics denseSphereHarmonics k i j G hG y).symm
end ShrinkingSpheres
