import Proof.ParallelNormAssemblyReservedNormalizedWords
import Proof.PhysicalPotentialFirstWordLifts

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2800000
set_option maxRecDepth 10000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set
open scoped ContDiff Topology
namespace ShrinkingSpheres.ParallelEnergy
open OAI.AnisotropicCalderon.SphereHarmonic

def normalizedCoordinateGeneratorCoefficients (d : Data) (y : X) :
    PhysicalPotentialGeneratorIndex → PhysicalPotentialGeneratorIndex → ℝ
  | .inl _,.inl _ => 1
  | .inr (.inl a),.inr (.inl j) => frameCoordinateLinear d.γ d.frame y j (axis a)
  | .inr (.inr a),.inr (.inr j) => (d.radius y)⁻¹*frameCoordinateLinear d.γ d.frame y j (axis a)
  | _,_ => 0

lemma normalized_generator_low_old_words {Y : Set X} {d : Data} {CF CT : ℝ}
    (P : PhysicalPrincipalData Y d CF CT) (y : X) (a : PhysicalPotentialGeneratorIndex) :
    normalizedPotentialGeneratorLow P y a=
      ∑ c : PhysicalPotentialGeneratorIndex,normalizedCoordinateGeneratorCoefficients d y a c •
        P.potentialGeneratorLow y c := by
  rcases a with u | (a | a)
  all_goals simp only [normalizedPotentialGeneratorLow,potentialGeneratorWeight,potentialCoordinateGeneratorLow,
    normalizedCoordinateGeneratorCoefficients,PhysicalPrincipalData.potentialGeneratorLow,
    Fintype.sum_sum_type,Fintype.sum_unique,zero_smul,one_smul,inv_one,Finset.sum_const_zero,
    zero_add,add_zero,one_mul,framedRaisingHalfL,Finset.smul_sum,smul_smul]

lemma normalized_generator_high_old_words {Y : Set X} {d : Data} {CF CT : ℝ}
    (P : PhysicalPrincipalData Y d CF CT) (y : X) (a : PhysicalPotentialGeneratorIndex) :
    normalizedPotentialGeneratorHigh P y a=
      ∑ c : PhysicalPotentialGeneratorIndex,normalizedCoordinateGeneratorCoefficients d y a c •
        P.potentialGeneratorHigh y c := by
  rcases a with u | (a | a)
  all_goals simp only [normalizedPotentialGeneratorHigh,potentialGeneratorWeight,potentialCoordinateGeneratorHigh,
    normalizedCoordinateGeneratorCoefficients,PhysicalPrincipalData.potentialGeneratorHigh,
    Fintype.sum_sum_type,Fintype.sum_unique,zero_smul,one_smul,inv_one,Finset.sum_const_zero,
    zero_add,add_zero,one_mul,framedRaisingHigherL,Finset.smul_sum,smul_smul]

lemma normalized_generator_balanced {Y : Set X} {d : Data} {CF CT : ℝ}
    (P : PhysicalPrincipalData Y d CF CT) {y : X} (hy : y ∈ Y) (a : PhysicalPotentialGeneratorIndex) :
    (sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)).comp
      (normalizedPotentialGeneratorHigh P y a)=
      (normalizedPotentialGeneratorLow P y a).comp
        (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)) := by
  rw [normalized_generator_high_old_words,normalized_generator_low_old_words]
  apply ContinuousLinearMap.ext
  intro u
  simp only [ContinuousLinearMap.comp_apply,_root_.sum_apply,_root_.smul_apply,map_sum,map_smul]
  apply Finset.sum_congr rfl
  intro c _
  exact congrArg (fun z => normalizedCoordinateGeneratorCoefficients d y a c • z)
    (DFunLike.congr_fun (P.potential_generator_balanced hy c) u)

def normalizedGeneratorForwardFirstWordHigherL {Y : Set X} {d : Data} {CF CT CG CK : ℝ}
    (P : PhysicalPrincipalData Y d CF CT) {y : X} (W : PhysicalPotentialQuarticData P y CG CK)
    (a : PhysicalPotentialGeneratorIndex) : SphereSobolev (5/2:ℝ) →L[ℝ] SphereSobolev (3/2:ℝ) :=
  ∑ c : PhysicalPotentialGeneratorIndex,normalizedCoordinateGeneratorCoefficients d y a c • W.forwardFirstWordHigherL c

/-- The actual normalized coordinate first word has its H3/2 lift from
the SAME W on the genuine H5/2 common core, with the true inclusion square. -/
lemma normalized_generator_forward_first_word_lift {Y : Set X} {d : Data} {CF CT CG CK : ℝ}
    (P : PhysicalPrincipalData Y d CF CT) {y : X} (hy : y ∈ Y)
    (W : PhysicalPotentialQuarticData P y CG CK) (a : PhysicalPotentialGeneratorIndex)
    (u : SphereSobolev (5/2:ℝ)) :
    sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)
      (normalizedGeneratorForwardFirstWordHigherL P W a u)=
      normalizedPotentialGeneratorHigh P y a
        (sphereSobolevInclusionL (5/2:ℝ) (3/2:ℝ) (by norm_num) u) := by
  rw [normalized_generator_high_old_words]
  simp only [normalizedGeneratorForwardFirstWordHigherL,_root_.sum_apply,_root_.smul_apply,map_sum,map_smul]
  apply Finset.sum_congr rfl
  intro c _
  exact congrArg (fun z => normalizedCoordinateGeneratorCoefficients d y a c • z)
    (W.forwardFirstWordHigherL_inclusion hy c u)

end ShrinkingSpheres.ParallelEnergy
