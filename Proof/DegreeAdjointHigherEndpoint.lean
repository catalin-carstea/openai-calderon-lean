import Proof.DegreeHalfCovariantData
import Proof.GradedGeneratorAdjoints
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
open scoped ContDiff
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.SphereHarmonic

lemma degreeHalfL_adjoint : degreeHalfL.adjoint=degreeHalfL :=
  sphereSobolevShiftedDegreeHalf_adjoint

/-- Degree uses its genuine shifted higher endpoint for the true adjoint. -/
lemma degreeHigherL_adjoint_pair :
    (sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)).comp degreeHigherL=
      degreeHalfL.adjoint.comp (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)) := by
  rw [degreeHalfL_adjoint]
  exact degreeHalf_balanced

lemma norm_degreeHigherL_le_two : ‖degreeHigherL‖ ≤ 2 :=
  norm_sphereSobolevShiftedDegreeL_le_two _
end ShrinkingSpheres
