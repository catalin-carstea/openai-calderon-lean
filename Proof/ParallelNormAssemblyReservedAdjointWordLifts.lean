import Proof.ParallelNormAssemblyReservedNormalizedWordLifts
import Proof.ParallelNormAssemblyReservedCubicCorePair

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2800000
set_option maxRecDepth 10000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set
open scoped ContDiff Topology InnerProductSpace
namespace ShrinkingSpheres.ParallelEnergy
open OAI.AnisotropicCalderon.SphereHarmonic

def normalizedGeneratorAdjointHigherL {Y : Set X} {d : Data} {CF CT CG CK : ℝ}
    (P : PhysicalPrincipalData Y d CF CT) {y : X} (W : PhysicalPotentialQuarticData P y CG CK)
    (a : PhysicalPotentialGeneratorIndex) : SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ) :=
  ∑ c : PhysicalPotentialGeneratorIndex,normalizedCoordinateGeneratorCoefficients d y a c • W.adjointHigh c

/-- The normalized true-adjoint word has its actual low/HIGH square.
Testing the adjoint against genuine half values avoids any grade coercion. -/
lemma normalized_generator_adjoint_high_balanced {Y : Set X} {d : Data} {CF CT CG CK : ℝ}
    (P : PhysicalPrincipalData Y d CF CT) {y : X} (W : PhysicalPotentialQuarticData P y CG CK)
    (a : PhysicalPotentialGeneratorIndex) :
    (sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)).comp (normalizedGeneratorAdjointHigherL P W a)=
      (normalizedPotentialGeneratorLow P y a).adjoint.comp
        (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)) := by
  apply ContinuousLinearMap.ext
  intro u
  apply ext_inner_right ℝ
  intro v
  simp only [ContinuousLinearMap.comp_apply]
  rw [(normalizedPotentialGeneratorLow P y a).adjoint_inner_left,normalized_generator_low_old_words]
  simp only [normalizedGeneratorAdjointHigherL,_root_.sum_apply,_root_.smul_apply,map_sum,map_smul,
    sum_inner,inner_sum,real_inner_smul_left,inner_smul_right]
  apply Finset.sum_congr rfl
  intro c _
  have hc := DFunLike.congr_fun (W.adjoint_compatible c) u
  simp only [ContinuousLinearMap.comp_apply] at hc
  exact congrArg (fun t => normalizedCoordinateGeneratorCoefficients d y a c*t)
    ((congrArg (fun z => ⟪z,v⟫_ℝ) hc).trans ((P.potentialGeneratorLow y c).adjoint_inner_left _ _))

def normalizedGeneratorReverseFirstWordHigherL {Y : Set X} {d : Data} {CF CT CG CK : ℝ}
    (P : PhysicalPrincipalData Y d CF CT) {y : X} (W : PhysicalPotentialQuarticData P y CG CK)
    (a : PhysicalPotentialGeneratorIndex) : SphereSobolev (5/2:ℝ) →L[ℝ] SphereSobolev (3/2:ℝ) :=
  ∑ c : PhysicalPotentialGeneratorIndex,normalizedCoordinateGeneratorCoefficients d y a c • W.reverseFirstWordHigherL c

/-- The SAME W produces the genuine reverse first-word lift for ANY
coherent normalized true-adjoint HIGH value. No lift family is differentiated. -/
lemma normalized_generator_reverse_first_word_lift {Y : Set X} {d : Data} {CF CT CG CK : ℝ}
    (P : PhysicalPrincipalData Y d CF CT) {y : X} (W : PhysicalPotentialQuarticData P y CG CK)
    (a : PhysicalPotentialGeneratorIndex)
    (AH : SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ))
    (hAH : (sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)).comp AH=
      (normalizedPotentialGeneratorLow P y a).adjoint.comp
        (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)))
    (u : SphereSobolev (5/2:ℝ)) :
    sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)
      (normalizedGeneratorReverseFirstWordHigherL P W a u)=
      AH (sphereSobolevInclusionL (5/2:ℝ) (3/2:ℝ) (by norm_num) u) := by
  have hSame : normalizedGeneratorAdjointHigherL P W a=AH := by
    apply ContinuousLinearMap.ext
    intro v
    apply sphereSobolevInclusionL_injective (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)
    exact DFunLike.congr_fun ((normalized_generator_adjoint_high_balanced P W a).trans hAH.symm) v
  rw [←hSame]
  simp only [normalizedGeneratorReverseFirstWordHigherL,normalizedGeneratorAdjointHigherL,
    _root_.sum_apply,_root_.smul_apply,map_sum,map_smul]
  apply Finset.sum_congr rfl
  intro c _
  exact congrArg (fun z => normalizedCoordinateGeneratorCoefficients d y a c • z)
    (W.reverseFirstWordHigherL_inclusion c u)

end ShrinkingSpheres.ParallelEnergy
