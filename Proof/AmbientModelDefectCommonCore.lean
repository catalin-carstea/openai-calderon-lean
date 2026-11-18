import Proof.ModelDefectFiveHalfSource
import Proof.CanonicalFirstModelDefectPoint

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped ContDiff
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.SphereHarmonic

lemma ambientHigherSobolevSection_higher_inclusion (s t : ℝ) (hs : s ≤ 4) (ht : t ≤ 4) (hst : t ≤ s)
    (G : X × X → ℝ) (hG : ContDiff ℝ ∞ G) (y : X) :
    sphereSobolevInclusionL s t hst (ambientHigherSobolevSection s hs G hG y)=
      ambientHigherSobolevSection t ht G hG y := by
  apply sphereSobolev_ext t
  intro k
  rw [sphereSobolevCoefficientL_inclusion,ambientHigherSobolevSection_coefficient,
    ambientHigherSobolevSection_coefficient]

/-- The potential and the scalar/first forms use the SAME actual smooth
model-defect source, joined by a genuine inclusion of the constructed cores. -/
lemma ambientModelDefectFiveHalfSection_two (d : Data) (G : X × X → ℝ) (hG : ContDiff ℝ ∞ G) (y : X) :
    sphereSobolevInclusionL (5/2:ℝ) 2 (by norm_num) (ambientModelDefectFiveHalfSection d G hG y)=
      ambientModelAdjointDefectSection d G hG y := by
  have hI : sphereSobolevInclusionL ((7/2:ℝ)-1) ((3:ℝ)-1) (by norm_num)=
      sphereSobolevInclusionL (5/2:ℝ) 2 (by norm_num) := by congr 1 <;> norm_num
  have hh := modelAdjointDefectSobolevL_inclusion (7/2:ℝ) 3 (by norm_num) d y
  rw [hI] at hh
  have hg := DFunLike.congr_fun hh (ambientHigherSobolevSection (7/2:ℝ) (by norm_num) G hG y)
  simp only [ContinuousLinearMap.comp_apply] at hg
  exact hg.symm.trans (congrArg (modelAdjointDefectSobolevL 3 d y)
    (ambientHigherSobolevSection_higher_inclusion (7/2:ℝ) 3 (by norm_num) (by norm_num) (by norm_num) G hG y))

end ShrinkingSpheres
