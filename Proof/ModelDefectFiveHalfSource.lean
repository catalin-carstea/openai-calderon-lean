import Proof.ModelAdjointDefectHigherCore
import Proof.AmbientHigherSobolevSupport
import Proof.CanonicalCoarseTripleEnergy

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set
open scoped ContDiff Topology
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.SphereHarmonic

def ambientModelDefectFiveHalfSection (d : Data) (G : X × X → ℝ) (hG : ContDiff ℝ ∞ G)
    (x : X) : SphereSobolev (5/2:ℝ) :=
  modelAdjointDefectSobolevL (7/2:ℝ) d x (ambientHigherSobolevSection (7/2:ℝ) (by norm_num) G hG x)

lemma ambientModelDefectFiveHalfSection_half (d : Data) (G : X × X → ℝ) (hG : ContDiff ℝ ∞ G) (x : X) :
    sphereSobolevInclusionL (5/2:ℝ) (1/2:ℝ) (by norm_num) (ambientModelDefectFiveHalfSection d G hG x)=
      modelAdjointDefectSobolevL (3/2:ℝ) d x (ambientSobolevSection (3/2:ℝ) (by norm_num) G hG x) := by
  have hI : sphereSobolevInclusionL ((7/2:ℝ)-1) ((3/2:ℝ)-1) (by norm_num)=
      sphereSobolevInclusionL (5/2:ℝ) (1/2:ℝ) (by norm_num) := by congr 1 <;> norm_num
  have hh := modelAdjointDefectSobolevL_inclusion (7/2:ℝ) (3/2:ℝ) (by norm_num) d x
  rw [hI] at hh
  have hg := DFunLike.congr_fun hh (ambientHigherSobolevSection (7/2:ℝ) (by norm_num) G hG x)
  simp only [ContinuousLinearMap.comp_apply] at hg
  have hSource := ambientHigherSobolevSection_inclusion (7/2:ℝ) (3/2:ℝ)
    (by norm_num) (by norm_num) (by norm_num) G hG x
  exact hg.symm.trans (congrArg (modelAdjointDefectSobolevL (3/2:ℝ) d x) hSource)

lemma norm_ambientModelDefectFiveHalfSection_half_le (d : Data) (G : X × X → ℝ)
    (hG : ContDiff ℝ ∞ G) (x : X)
    (hFrame : ∀ i j,metricPair d.γ x (d.frame x i) (d.frame x j)=if i=j then 1 else 0) :
    ‖sphereSobolevInclusionL (5/2:ℝ) (1/2:ℝ) (by norm_num) (ambientModelDefectFiveHalfSection d G hG x)‖ ≤
      (∑ i : I,‖flatLoweringSobolevL (3/2:ℝ) i‖)*beta d.γ d.radius x*
        ‖ambientSobolevSection (3/2:ℝ) (by norm_num) G hG x‖ := by
  rw [ambientModelDefectFiveHalfSection_half]
  exact ((modelAdjointDefectSobolevL (3/2:ℝ) d x).le_opNorm _).trans
    (mul_le_mul_of_nonneg_right (norm_modelAdjointDefectSobolevL_le (3/2:ℝ) d x hFrame) (norm_nonneg _))

theorem contDiff_supported_ambientModelDefectFiveHalfSection {Y : Set X} (hY : IsOpen Y)
    (d : Data) (G : X × X → ℝ) (hG : ContDiff ℝ ∞ G)
    (hlog : ContDiffOn ℝ ∞ (fun x => Real.log (d.radius x)) Y)
    (he : ∀ i,ContDiffOn ℝ ∞ (fun x => d.frame x i) Y)
    (S : Set X) (hS : IsClosed S) (hSY : S ⊆ Y)
    (h0 : ∀ x ∉ S,ambientSobolevSection 2 (by norm_num) G hG x=0) :
    ContDiff ℝ ∞ (ambientModelDefectFiveHalfSection d G hG) ∧
      ∀ x ∉ S,ambientModelDefectFiveHalfSection d G hG x=0 := by
  let V := ambientHigherSobolevSection (7/2:ℝ) (by norm_num) G hG
  have hV : ContDiff ℝ ∞ V := contDiff_ambientHigherSobolevSection (7/2:ℝ) (by norm_num) G hG
  have hV0 (x : X) (hx : x ∉ S) : V x=0 :=
    ambientHigherSobolevSection_zero_of_coarse (7/2:ℝ) 2 (by norm_num) (by norm_num) (by norm_num) G hG (h0 x hx)

  exact contDiff_supported_modelAdjointDefectSobolevL_apply hY (7/2:ℝ) d hlog he V hV S hS hSY hV0

end ShrinkingSpheres
