import Proof.PhysicalPotentialFirstWordLifts

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.SphereHarmonic

/-- The shared norm calculation for genuine degree-graph lifts of both
forward and reverse first words. -/
lemma norm_degree_graph_first_word_lift_le
    (A C : SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ))
    (a c : ℝ) (hA : ‖A‖ ≤ a) (hC : ‖C‖ ≤ c) :
    ‖(sphereSobolevBesselOrderL (1/2:ℝ) (3/2:ℝ)).comp
      (A.comp (sphereSobolevShiftedDegreeL (5/2:ℝ))+
        C.comp (sphereSobolevInclusionL (5/2:ℝ) (3/2:ℝ) (by norm_num))+
        A.comp (sphereSobolevInclusionL (5/2:ℝ) (3/2:ℝ) (by norm_num)))‖ ≤ 3*a+c := by
  let J := sphereSobolevInclusionL (5/2:ℝ) (3/2:ℝ) (by norm_num)
  let D := sphereSobolevShiftedDegreeL (5/2:ℝ)
  have hAD : ‖A.comp D‖ ≤ a*2 := (ContinuousLinearMap.opNorm_comp_le _ _).trans
    (mul_le_mul hA (norm_sphereSobolevShiftedDegreeL_le_two (5/2:ℝ)) (norm_nonneg _) ((norm_nonneg _).trans hA))
  have hCJ : ‖C.comp J‖ ≤ c := (ContinuousLinearMap.opNorm_comp_le _ _).trans
    ((mul_le_mul hC (norm_sphereSobolevInclusionL_le (5/2:ℝ) (3/2:ℝ) (by norm_num))
      (norm_nonneg _) ((norm_nonneg _).trans hC)).trans_eq (mul_one _))
  have hAJ : ‖A.comp J‖ ≤ a := (ContinuousLinearMap.opNorm_comp_le _ _).trans
    ((mul_le_mul hA (norm_sphereSobolevInclusionL_le (5/2:ℝ) (3/2:ℝ) (by norm_num))
      (norm_nonneg _) ((norm_nonneg _).trans hA)).trans_eq (mul_one _))
  calc
    _ ≤ ‖sphereSobolevBesselOrderL (1/2:ℝ) (3/2:ℝ)‖*‖A.comp D+C.comp J+A.comp J‖ :=
      ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ 1*‖A.comp D+C.comp J+A.comp J‖ :=
      mul_le_mul_of_nonneg_right (norm_sphereSobolevBesselOrderL_le (1/2:ℝ) (3/2:ℝ)) (norm_nonneg _)
    _ ≤ (a*2+c)+a := by
      rw [one_mul]
      exact (norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans (add_le_add hAD hCJ)) hAJ)
    _ = _ := by ring

lemma PhysicalPotentialQuarticData.norm_forwardFirstWordHigherL_le
    {Y : Set X} {d : Data} {CF CT CG CK : ℝ} {P : PhysicalPrincipalData Y d CF CT} {y : X}
    (W : PhysicalPotentialQuarticData P y CG CK) (hy : y ∈ Y)
    (hr : 0 ≤ d.radius y) (a : PhysicalPotentialGeneratorIndex) :
    ‖W.forwardFirstWordHigherL a‖ ≤ (3*physicalPotentialGeneratorBudget CF+CK)*potentialGeneratorWeight (d.radius y) a := by
  let A := P.potentialGeneratorHigh y a
  let C := W.commHigh (.inl ()) a
  let J := sphereSobolevInclusionL (5/2:ℝ) (3/2:ℝ) (by norm_num)
  let D := sphereSobolevShiftedDegreeL (5/2:ℝ)
  have hC : ‖C‖ ≤ CK*potentialGeneratorWeight (d.radius y) a := by
    simpa only [C,potentialGeneratorWeight,mul_one] using W.commHigh_bound (.inl ()) a
  have hh := norm_degree_graph_first_word_lift_le A C _ _ (P.potential_generator_norm_bounds hy hr a).2 hC
  change ‖(sphereSobolevBesselOrderL (1/2:ℝ) (3/2:ℝ)).comp (C.comp J+A.comp D+A.comp J)‖ ≤ _
  rw [add_comm (C.comp J) (A.comp D)]
  exact hh.trans_eq (by ring)

end ShrinkingSpheres
