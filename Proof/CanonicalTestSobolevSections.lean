import Proof.CanonicalSmoothSobolevSection
import Proof.PartialEnergyBounds
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxSynthPendingDepth 25
open Set
open scoped ContDiff Topology
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.SphereHarmonic OAI.AnisotropicCalderon.SmoothAngularApplication

lemma ambientSobolevSection_eq_zero_off (s : ℝ) (hs : s ≤ 2) (G : X × X → ℝ) (hG : ContDiff ℝ ∞ G)
    (S : Set X) (hZero : ∀ x ∉ S,∀ w : UnitSphere,G (x,w.val)=0) {x : X} (hx : x ∉ S) :
    ambientSobolevSection s hs G hG x=0 := by
  unfold ambientSobolevSection
  rw [ambientBesselField_eq_zero orthogonalSphereHarmonics denseSphereHarmonics s hs G hG S hZero x hx,map_zero,map_zero]

namespace HarmonicTestExpansion
variable {Y : Set X} {g : MetricField} {e : Frame} {φ : Field}

def realSobolevSection (E : HarmonicTestExpansion Y g e φ) (s : ℝ) (hs : s ≤ 2) : X → SphereSobolev s :=
  ambientSobolevSection s hs (fun p => (E.representative p).re) (Complex.reCLM.contDiff.comp E.representativeSmooth)

def imagSobolevSection (E : HarmonicTestExpansion Y g e φ) (s : ℝ) (hs : s ≤ 2) : X → SphereSobolev s :=
  ambientSobolevSection s hs (fun p => (E.representative p).im) (Complex.imCLM.contDiff.comp E.representativeSmooth)

lemma contDiff_realSobolevSection (E : HarmonicTestExpansion Y g e φ) (s : ℝ) (hs : s ≤ 2) :
    ContDiff ℝ ∞ (E.realSobolevSection s hs) := contDiff_ambientSobolevSection s hs _ _
lemma contDiff_imagSobolevSection (E : HarmonicTestExpansion Y g e φ) (s : ℝ) (hs : s ≤ 2) :
    ContDiff ℝ ∞ (E.imagSobolevSection s hs) := contDiff_ambientSobolevSection s hs _ _

lemma realSobolevSection_zero (E : HarmonicTestExpansion Y g e φ) (s : ℝ) (hs : s ≤ 2) {x : X} (hx : x ∉ E.supportSet) :
    E.realSobolevSection s hs x=0 := by
  apply ambientSobolevSection_eq_zero_off s hs _ _ E.supportSet _ hx
  intro y hy w
  rw [E.representativeZero y hy w,Complex.zero_re]
lemma imagSobolevSection_zero (E : HarmonicTestExpansion Y g e φ) (s : ℝ) (hs : s ≤ 2) {x : X} (hx : x ∉ E.supportSet) :
    E.imagSobolevSection s hs x=0 := by
  apply ambientSobolevSection_eq_zero_off s hs _ _ E.supportSet _ hx
  intro y hy w
  rw [E.representativeZero y hy w,Complex.zero_im]

lemma norm_realSobolevSection (E : HarmonicTestExpansion Y g e φ) (s : ℝ) (hs : s ≤ 2) (x : X) :
    ‖E.realSobolevSection s hs x‖=‖E.realBessel s hs x‖ := norm_ambientSobolevSection s hs _ _ x
lemma norm_imagSobolevSection (E : HarmonicTestExpansion Y g e φ) (s : ℝ) (hs : s ≤ 2) (x : X) :
    ‖E.imagSobolevSection s hs x‖=‖E.imagBessel s hs x‖ := norm_ambientSobolevSection s hs _ _ x

lemma sobolev_eq_native_sections (E : HarmonicTestExpansion Y g e φ)
    (hFrame : ∀ x ∈ Y,∀ i j,metricPair g x (e x i) (e x j)=if i=j then 1 else 0)
    (s : ℝ) (hs : s ≤ 2) {x : X} (hx : x ∈ Y) :
    sobolevSq g e s x (fun w => φ (x,w))=‖E.realSobolevSection s hs x‖^2+‖E.imagSobolevSection s hs x‖^2 := by
  rw [norm_realSobolevSection,norm_imagSobolevSection]
  exact E.sobolev_eq_besselSquare hFrame s hs hx
end HarmonicTestExpansion
end ShrinkingSpheres
