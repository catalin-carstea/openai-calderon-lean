import Proof.PhysicalPotentialWordMatrix
import Proof.DegreeHalfCovariantData
import Proof.HalfCovariantWeightedCombination
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option maxSynthPendingDepth 30
open Set
open scoped ContDiff
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.SphereHarmonic

def potentialGeneratorWeight (r : ℝ) : PhysicalPotentialGeneratorIndex → ℝ
  | .inl _ => 1
  | .inr (.inl _) => 1
  | .inr (.inr _) => r

def physicalPotentialGeneratorBudget (CF : ℝ) : ℝ :=
  2+10*radialDriftSobolevBound (-(1/2:ℝ))+10*radialDriftSobolevBound (-(3/2:ℝ))+|CF|

lemma physicalPotentialGeneratorBudget_bounds (CF : ℝ) :
    2 ≤ physicalPotentialGeneratorBudget CF ∧
      10*radialDriftSobolevBound (-(1/2:ℝ)) ≤ physicalPotentialGeneratorBudget CF ∧
      10*radialDriftSobolevBound (-(3/2:ℝ)) ≤ physicalPotentialGeneratorBudget CF ∧
      |CF| ≤ physicalPotentialGeneratorBudget CF := by
  have hL : 0 ≤ radialDriftSobolevBound (-(1/2:ℝ)) := zero_le_one.trans (le_max_left _ _)
  have hH : 0 ≤ radialDriftSobolevBound (-(3/2:ℝ)) := zero_le_one.trans (le_max_left _ _)
  unfold physicalPotentialGeneratorBudget
  exact ⟨by linarith [abs_nonneg CF],by linarith [abs_nonneg CF],by linarith [abs_nonneg CF],by linarith⟩

lemma potentialGeneratorWeight_nonneg {r : ℝ} (hr : 0 ≤ r) (a : PhysicalPotentialGeneratorIndex) :
    0 ≤ potentialGeneratorWeight r a := by
  rcases a with u | (i | i) <;> exact (by norm_num [potentialGeneratorWeight] <;> exact hr)

namespace PhysicalPrincipalData
variable {Y : Set X} {d : Data} {CF CT : ℝ}

lemma potential_generator_norm_bounds (P : PhysicalPrincipalData Y d CF CT)
    {y : X} (hy : y ∈ Y) (hr : 0 ≤ d.radius y) (a : PhysicalPotentialGeneratorIndex) :
    ‖P.potentialGeneratorLow y a‖ ≤ physicalPotentialGeneratorBudget CF*potentialGeneratorWeight (d.radius y) a ∧
      ‖P.potentialGeneratorHigh y a‖ ≤ physicalPotentialGeneratorBudget CF*potentialGeneratorWeight (d.radius y) a := by
  have hB := physicalPotentialGeneratorBudget_bounds CF
  rcases a with u | (i | i)
  · exact ⟨(norm_sphereSobolevShiftedDegreeL_le_two _).trans (by simpa only [potentialGeneratorWeight,mul_one] using hB.1),
      (norm_sphereSobolevShiftedDegreeL_le_two _).trans (by simpa only [potentialGeneratorWeight,mul_one] using hB.1)⟩
  · exact ⟨(norm_flatHalfRaisingL_le i).trans (by simpa only [potentialGeneratorWeight,mul_one] using hB.2.1),
      (norm_flatThreeHalfRaisingL_le i).trans (by simpa only [potentialGeneratorWeight,mul_one] using hB.2.2.1)⟩
  · have hCF : CF ≤ physicalPotentialGeneratorBudget CF := (le_abs_self _).trans hB.2.2.2
    exact ⟨(P.first.low_bound i y hy).trans (mul_le_mul_of_nonneg_right hCF hr),
      (P.first.high_bound i y hy).trans (mul_le_mul_of_nonneg_right hCF hr)⟩

lemma potential_generator_smooth (P : PhysicalPrincipalData Y d CF CT) (a : PhysicalPotentialGeneratorIndex) :
    ContDiffOn ℝ ∞ (fun y => P.potentialGeneratorLow y a) Y ∧
      ContDiffOn ℝ ∞ (fun y => P.potentialGeneratorHigh y a) Y := by
  rcases a with u | (i | i)
  · exact ⟨contDiffOn_const,contDiffOn_const⟩
  · exact ⟨contDiffOn_const,contDiffOn_const⟩
  · exact ⟨P.first.low_smooth i,P.first.high_smooth i⟩

lemma potential_generator_balanced (P : PhysicalPrincipalData Y d CF CT)
    {y : X} (hy : y ∈ Y) (a : PhysicalPotentialGeneratorIndex) :
    (sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)).comp (P.potentialGeneratorHigh y a)=
      (P.potentialGeneratorLow y a).comp (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)) := by
  rcases a with u | (i | i)
  · exact degreeHalf_balanced
  · have h := (flatRaisingSobolevL_inclusion (3/2:ℝ) (1/2:ℝ) (by norm_num) i).symm
    have hI : sphereSobolevInclusionL ((3/2:ℝ)-1) ((1/2:ℝ)-1) (by norm_num)=
        sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num) := by congr 1 <;> norm_num
    rw [hI] at h
    exact h
  · exact balanced_endpoint_pair_of_coarse _ _ _ (P.first.low_coarse i y hy) (P.first.high_coarse i y hy)
end PhysicalPrincipalData
end ShrinkingSpheres
