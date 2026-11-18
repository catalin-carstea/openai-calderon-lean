import Proof.AmbientHigherSobolevSection

noncomputable section
set_option autoImplicit false
open scoped ContDiff
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.SphereHarmonic

lemma ambientHigherSobolevSection_zero_of_coarse (s t : ℝ) (hs : s ≤ 4) (ht : t ≤ 2) (hst : t ≤ s)
    (G : X × X → ℝ) (hG : ContDiff ℝ ∞ G) {y : X} (h0 : ambientSobolevSection t ht G hG y=0) :
    ambientHigherSobolevSection s hs G hG y=0 := by
  apply sphereSobolevInclusionL_injective s t hst
  rw [ambientHigherSobolevSection_inclusion s t hs ht hst G hG y,h0,map_zero]

end ShrinkingSpheres
