import Proof.AmbientHigherSobolevSupport
import Proof.CanonicalTestSobolevSections

noncomputable section
set_option autoImplicit false
open Set
open scoped ContDiff
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.SphereHarmonic
namespace HarmonicTestExpansion
variable {Y : Set X} {g : MetricField} {e : Frame} {φ : Field}

def realHigherSobolevSection (E : HarmonicTestExpansion Y g e φ) (s : ℝ) (hs : s ≤ 4) : X → SphereSobolev s :=
  ambientHigherSobolevSection s hs (fun p => (E.representative p).re) (Complex.reCLM.contDiff.comp E.representativeSmooth)

def imagHigherSobolevSection (E : HarmonicTestExpansion Y g e φ) (s : ℝ) (hs : s ≤ 4) : X → SphereSobolev s :=
  ambientHigherSobolevSection s hs (fun p => (E.representative p).im) (Complex.imCLM.contDiff.comp E.representativeSmooth)

lemma contDiff_realHigherSobolevSection (E : HarmonicTestExpansion Y g e φ) (s : ℝ) (hs : s ≤ 4) :
    ContDiff ℝ ∞ (E.realHigherSobolevSection s hs) := contDiff_ambientHigherSobolevSection s hs _ _

lemma contDiff_imagHigherSobolevSection (E : HarmonicTestExpansion Y g e φ) (s : ℝ) (hs : s ≤ 4) :
    ContDiff ℝ ∞ (E.imagHigherSobolevSection s hs) := contDiff_ambientHigherSobolevSection s hs _ _

lemma realHigherSobolevSection_inclusion (E : HarmonicTestExpansion Y g e φ)
    (s t : ℝ) (hs : s ≤ 4) (ht : t ≤ 2) (hst : t ≤ s) (y : X) :
    sphereSobolevInclusionL s t hst (E.realHigherSobolevSection s hs y)=E.realSobolevSection t ht y :=
  ambientHigherSobolevSection_inclusion s t hs ht hst _ _ y

lemma imagHigherSobolevSection_inclusion (E : HarmonicTestExpansion Y g e φ)
    (s t : ℝ) (hs : s ≤ 4) (ht : t ≤ 2) (hst : t ≤ s) (y : X) :
    sphereSobolevInclusionL s t hst (E.imagHigherSobolevSection s hs y)=E.imagSobolevSection t ht y :=
  ambientHigherSobolevSection_inclusion s t hs ht hst _ _ y

lemma realHigherSobolevSection_zero (E : HarmonicTestExpansion Y g e φ)
    (s : ℝ) (hs : s ≤ 4) (hs0 : 0 ≤ s) {y : X} (hy : y ∉ E.supportSet) :
    E.realHigherSobolevSection s hs y=0 :=
  ambientHigherSobolevSection_zero_of_coarse s 0 hs (by norm_num) hs0 _ _
    (E.realSobolevSection_zero 0 (by norm_num) hy)

lemma imagHigherSobolevSection_zero (E : HarmonicTestExpansion Y g e φ)
    (s : ℝ) (hs : s ≤ 4) (hs0 : 0 ≤ s) {y : X} (hy : y ∉ E.supportSet) :
    E.imagHigherSobolevSection s hs y=0 :=
  ambientHigherSobolevSection_zero_of_coarse s 0 hs (by norm_num) hs0 _ _
    (E.imagSobolevSection_zero 0 (by norm_num) hy)

end HarmonicTestExpansion
end ShrinkingSpheres
