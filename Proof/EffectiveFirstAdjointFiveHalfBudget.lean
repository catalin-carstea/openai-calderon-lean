import Proof.EffectiveFirstAdjointFiveHalf
import Proof.PotentialFirstWordHigherBounds

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
open Set
open scoped ContDiff Topology
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.SphereHarmonic

def firstAdjointFiveHalfFrameBudget (d : Data) (CG CK : ℝ) (j : I) (y : X) : ℝ :=
  let q := frameTensorMatrix d.γ d.frame y (principal d.γ d.g₂ y)
  let H := (3*CG+CK)*(1+|d.radius y|)
  (∑ i : I,|(q i j+q j i)*scaledFrameLogRadius d.radius d.frame i y| *H)+
    2*(∑ i : I,|q i j-(if i=j then 1 else 0)| *H)+
    |d.radius y| *(∑ i : I,|q i j+q j i| *(‖firstFrameCorrectionAdjointFiveHalfL d y i‖+H))

def firstAdjointFiveHalfCoordinateBudget (d : Data) (CG CK : ℝ) (b : I) (y : X) : ℝ :=
  (∑ j : I,|d.frame y j b| *firstAdjointFiveHalfFrameBudget d CG CK j y)+
    |scalarPrincipalConnectionWeight d b y|

lemma PhysicalPotentialQuarticData.norm_reverseFirstWordHigherL_le_common
    {Y : Set X} {d : Data} {CF CT CG CK : ℝ} {P : PhysicalPrincipalData Y d CF CT} {y : X}
    (W : PhysicalPotentialQuarticData P y CG CK) (hCG : 0 ≤ CG) (hCK : 0 ≤ CK)
    (hr : 0 ≤ d.radius y) (a : PhysicalPotentialGeneratorIndex) :
    ‖W.reverseFirstWordHigherL a‖ ≤ (3*CG+CK)*(1+|d.radius y|) := by
  have hw : potentialGeneratorWeight (d.radius y) a ≤ 1+|d.radius y| := by
    rcases a with a|a
    · simp only [potentialGeneratorWeight];linarith only [abs_nonneg (d.radius y)]
    · rcases a with a|a
      · simp only [potentialGeneratorWeight];linarith only [abs_nonneg (d.radius y)]
      · simp only [potentialGeneratorWeight];linarith only [le_abs_self (d.radius y)]
  exact (W.norm_reverseFirstWordHigherL_le hCG hCK hr a).trans
    (mul_le_mul_of_nonneg_left hw (by positivity))

lemma PhysicalPrincipalData.norm_firstDerivativeAdjointFiveHalfL_le_budget
    {Y : Set X} {d : Data} {CF CT CG CK : ℝ} (P : PhysicalPrincipalData Y d CF CT)
    {y : X} (W : PhysicalPotentialQuarticData P y CG CK) (hCG : 0 ≤ CG) (hCK : 0 ≤ CK)
    (hr : 0 ≤ d.radius y) (j : I) :
    ‖P.firstDerivativeAdjointFiveHalfL W j‖ ≤ firstAdjointFiveHalfFrameBudget d CG CK j y := by
  let q := frameTensorMatrix d.γ d.frame y (principal d.γ d.g₂ y)
  let H := (3*CG+CK)*(1+|d.radius y|)
  have hw := W.norm_reverseFirstWordHigherL_le_common hCG hCK hr
  have h0 : ‖∑ i : I,((q i j+q j i)*scaledFrameLogRadius d.radius d.frame i y) •
      W.reverseFirstWordHigherL (.inl ())‖ ≤
      ∑ i : I,|(q i j+q j i)*scaledFrameLogRadius d.radius d.frame i y| *H :=
    (norm_sum_le _ _).trans (Finset.sum_le_sum (fun i _ => by
      rw [norm_smul,Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_left (hw (.inl ())) (abs_nonneg _)))
  have h1 : ‖∑ i : I,(q i j-(if i=j then 1 else 0)) • W.reverseFirstWordHigherL (.inr (.inl i))‖ ≤
      ∑ i : I,|q i j-(if i=j then 1 else 0)| *H :=
    (norm_sum_le _ _).trans (Finset.sum_le_sum (fun i _ => by
      rw [norm_smul,Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_left (hw (.inr (.inl i))) (abs_nonneg _)))
  have h2 : ‖∑ i : I,(q i j+q j i) •
      (firstFrameCorrectionAdjointFiveHalfL d y i+W.reverseFirstWordHigherL (.inr (.inr i)))‖ ≤
      ∑ i : I,|q i j+q j i| *(‖firstFrameCorrectionAdjointFiveHalfL d y i‖+H) :=
    (norm_sum_le _ _).trans (Finset.sum_le_sum (fun i _ => by
      rw [norm_smul,Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_left
        ((norm_add_le _ _).trans (add_le_add le_rfl (hw (.inr (.inr i))))) (abs_nonneg _)))
  unfold PhysicalPrincipalData.firstDerivativeAdjointFiveHalfL firstAdjointFiveHalfFrameBudget
  apply (norm_add_le _ _).trans
  apply add_le_add
  · apply (norm_add_le _ _).trans
    refine add_le_add h0 ?_
    rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2)]
    exact mul_le_mul_of_nonneg_left h1 (by norm_num)
  · rw [norm_smul,Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left h2 (abs_nonneg _)

lemma PhysicalPrincipalData.norm_firstCovariantCoordinateAdjointFiveHalfL_le_budget
    {Y : Set X} {d : Data} {CF CT CG CK : ℝ} (P : PhysicalPrincipalData Y d CF CT)
    {y : X} (W : PhysicalPotentialQuarticData P y CG CK) (hCG : 0 ≤ CG) (hCK : 0 ≤ CK)
    (hr : 0 ≤ d.radius y) (b : I) :
    ‖P.firstCovariantCoordinateAdjointFiveHalfL W b‖ ≤ firstAdjointFiveHalfCoordinateBudget d CG CK b y := by
  unfold PhysicalPrincipalData.firstCovariantCoordinateAdjointFiveHalfL
    PhysicalPrincipalData.firstCoordinateAdjointFiveHalfL firstAdjointFiveHalfCoordinateBudget
  apply (norm_sub_le _ _).trans
  apply add_le_add
  · exact (norm_sum_le _ _).trans (Finset.sum_le_sum (fun j _ => by
      rw [norm_smul,Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_left (P.norm_firstDerivativeAdjointFiveHalfL_le_budget W hCG hCK hr j) (abs_nonneg _)))
  · rw [norm_smul,Real.norm_eq_abs]
    exact ((mul_le_mul_of_nonneg_left
      (norm_sphereSobolevInclusionL_le (5/2:ℝ) (3/2:ℝ) (by norm_num)) (abs_nonneg _))).trans_eq (mul_one _)

end ShrinkingSpheres
