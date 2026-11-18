import Proof.ShiftedDegreeInclusion
import Proof.BalancedDegreeCommutator
import Proof.CovariantHalfCoarseBridge
import Proof.BalancedCoarsePotential
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
open Filter
open scoped Topology ContDiff
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.SphereHarmonic

/-- Normalize the genuine shifted degree endpoint without identifying
    Sobolev spaces of different orders. -/
def degreeHalfL : SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ)) :=
  sphereSobolevShiftedDegreeL (1/2:ℝ)

def degreeHigherL : SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ) :=
  sphereSobolevShiftedDegreeL (3/2:ℝ)

lemma degreeHalfL_coarse :
    (sphereSobolevInclusionL 0 (-(1/2:ℝ)) (by norm_num)).comp sphereSobolevDegreeL=
      degreeHalfL.comp (sphereSobolevInclusionL 1 (1/2:ℝ) (by norm_num)) :=
  ContinuousLinearMap.ext sphereSobolevDegreeL_half

lemma degreeHigherL_coarse :
    (sphereSobolevInclusionL (1/2:ℝ) 0 (by norm_num)).comp degreeHigherL=
      sphereSobolevDegreeL.comp (sphereSobolevInclusionL (3/2:ℝ) 1 (by norm_num)) := by
  apply ContinuousLinearMap.ext
  intro u
  have h := sphereSobolevShiftedDegreeL_inclusion (3/2:ℝ) 1 (by norm_num) u
  rw [sphereSobolevShiftedDegreeL_one_eq_degree] at h
  have hI : sphereSobolevInclusionL ((3/2:ℝ)-1) ((1:ℝ)-1) (by norm_num)=
      sphereSobolevInclusionL (1/2:ℝ) 0 (by norm_num) := by congr 1 <;> norm_num
  rw [hI] at h
  exact h

lemma degreeHalf_balanced :
    (sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)).comp degreeHigherL=
      degreeHalfL.comp (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)) :=
  balanced_endpoint_pair_of_coarse _ _ _ degreeHalfL_coarse degreeHigherL_coarse

lemma degreeHalf_covariant_derivative_zero (d : Data) (y a : X) :
    halfOperatorCovariantDerivativeL d (fun _ => degreeHalfL) (fun _ => degreeHigherL) y a=0 := by
  have hEq := halfOperatorCovariantDerivativeL_eq_coarse (fun _ => sphereSobolevDegreeL)
    (fun _ => degreeHalfL) (fun _ => degreeHigherL) 0
    (differentiableAt_const _) (differentiableAt_const _) (Eventually.of_forall (fun _ => degreeHalfL_coarse))
    degreeHigherL_coarse (sphereSobolevDegreeL_covariant_graph d y a)
  apply norm_eq_zero.mp
  apply le_antisymm ?_ (norm_nonneg _)
  rw [hEq]
  exact (norm_balancedCoarsePotentialL_le (0 : SphereSobolev 1 →L[ℝ] SphereSobolev 0)).trans_eq (norm_zero)
end ShrinkingSpheres
