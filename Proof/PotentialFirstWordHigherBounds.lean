import Proof.PotentialFirstWordNormEstimate
import Proof.Archive.SphereSobolevBesselOrderCompatibility

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.SphereHarmonic

/-- The constructed genuine first-word adjoint lift has a common bound
retaining the original generator's radius weight. -/
lemma PhysicalPotentialQuarticData.norm_reverseFirstWordHigherL_le
    {Y : Set X} {d : Data} {CF CT CG CK : ℝ} {P : PhysicalPrincipalData Y d CF CT} {y : X}
    (W : PhysicalPotentialQuarticData P y CG CK) (hCG : 0 ≤ CG) (hCK : 0 ≤ CK)
    (hr : 0 ≤ d.radius y) (a : PhysicalPotentialGeneratorIndex) :
    ‖W.reverseFirstWordHigherL a‖ ≤ (3*CG+CK)*potentialGeneratorWeight (d.radius y) a := by
  let C := -W.commHigh a (.inl ())
  have hC : ‖C‖ ≤ CK*potentialGeneratorWeight (d.radius y) a := by
    simpa only [C,norm_neg,potentialGeneratorWeight,mul_one] using W.commHigh_bound a (.inl ())
  have hh := norm_degree_graph_first_word_lift_le (W.adjointHigh a) C _ _ (W.adjoint_bound a) hC
  have hForm : W.reverseFirstWordHigherL a=
      (sphereSobolevBesselOrderL (1/2:ℝ) (3/2:ℝ)).comp
        ((W.adjointHigh a).comp (sphereSobolevShiftedDegreeL (5/2:ℝ))+
          C.comp (sphereSobolevInclusionL (5/2:ℝ) (3/2:ℝ) (by norm_num))+
          (W.adjointHigh a).comp (sphereSobolevInclusionL (5/2:ℝ) (3/2:ℝ) (by norm_num))) := by
    simp only [PhysicalPotentialQuarticData.reverseFirstWordHigherL,C,
      ContinuousLinearMap.neg_comp,sub_eq_add_neg]
  rw [hForm]
  exact hh.trans_eq (by ring)

end ShrinkingSpheres
