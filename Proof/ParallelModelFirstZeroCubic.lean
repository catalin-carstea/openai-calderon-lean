import Proof.ParallelModelFirstZeroWords
import Proof.ParallelModelFirstLeadingAlgebra
import Proof.ParallelNormAssemblyReservedNormalizedWordLifts

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2800000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
open Set
open scoped InnerProductSpace
namespace ShrinkingSpheres.ParallelEnergy
open OAI.AnisotropicCalderon.SphereHarmonic

/-- Actual one-word/model-zero comparison on the SAME genuine H5/2
source. The reverse word has its exact degree-minus-one shift. -/
theorem model_first_zero_raw_word_pair_identity
    {Y : Set X} {d : Data} {CF CT CG CK : ℝ}
    (P : PhysicalPrincipalData Y d CF CT) {y : X} (hy : y ∈ Y) (W : PhysicalPotentialQuarticData P y CG CK)
    (c : I) (a : PhysicalPotentialGeneratorIndex) (u5 : SphereSobolev (5/2:ℝ)) (h : SphereSobolev (3/2:ℝ)) :
    let Z := sphereSobolevInclusionL (1/2:ℝ) 0 (by norm_num);
    let u := sphereSobolevInclusionL (5/2:ℝ) (3/2:ℝ) (by norm_num) u5;
    ⟪Z (framedRaisingHigherL d y (axis c) (scalarModelDegreeSection (fun _ : X => u5) 0)),Z (P.potentialGeneratorHigh y a h)⟫_ℝ-
      sphereSobolevDualPairing (1/2:ℝ) (W.adjointHigh a u) (modelFirstZeroAdjointWeakL d c y h)=
      sphereSobolevDualPairing (1/2:ℝ) (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num) h)
        (cubicWordCommutatorValue P W a (modelFirstZeroWordCoefficient d c y) u) := by
  let u := sphereSobolevInclusionL (5/2:ℝ) (3/2:ℝ) (by norm_num) u5
  let V := fun e : PhysicalPotentialGeneratorIndex => W.forwardFirstWordHigherL e u5
  let v := W.reverseFirstWordHigherL a u5
  have hV (e : PhysicalPotentialGeneratorIndex) : sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num) (V e)=P.potentialGeneratorHigh y e u :=
    W.forwardFirstWordHigherL_inclusion hy e u5
  have hv : sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num) v=W.adjointHigh a u :=
    W.reverseFirstWordHigherL_inclusion a u5
  have hCore := cubic_word_commutator_core_identity P hy W a (modelFirstZeroWordCoefficient d c y) u V v hV hv
  rw [model_first_zero_forward_core_word P c y u5 V hV] at hCore
  change (P.potentialGeneratorLow y a).adjoint
    (framedRaisingHigherL d y (axis c) (scalarModelDegreeSection (fun _ : X => u5) 0))-
      quadraticWordForwardWeakValue P y (modelFirstZeroWordCoefficient d c y) v=_ at hCore
  have hA := quadratic_word_weak_adjunction P hy W (modelFirstZeroWordCoefficient d c y) v h
  rw [model_first_zero_adjoint_weak_word P hy W c h,hv] at hA
  have hPair := first_half_adjoint_pair_eq_physical_inner (P.potentialGeneratorLow y a) (P.potentialGeneratorHigh y a)
    (P.potential_generator_balanced hy a) h
    (framedRaisingHigherL d y (axis c) (scalarModelDegreeSection (fun _ : X => u5) 0))
  have hCore' := sub_eq_iff_eq_add.mp hCore
  rw [hCore'] at hPair
  have hPairPhysical := (real_inner_comm _ _).trans hPair.symm
  simp only [sphereSobolevDualPairing,inner_add_right] at hPairPhysical hA ⊢
  dsimp only [u] at hPairPhysical hA
  linarith only [hPairPhysical,hA]

def modelFirstNormalizedAdjointHigh {Y : Set X} {d : Data} {CF CT CG CK : ℝ}
    (P : PhysicalPrincipalData Y d CF CT) {y : X} (W : PhysicalPotentialQuarticData P y CG CK)
    (a : PhysicalPotentialGeneratorIndex) : SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ) :=
  ∑ e : PhysicalPotentialGeneratorIndex,normalizedCoordinateGeneratorCoefficients d y a e • W.adjointHigh e

def modelFirstNormalizedZeroCommutatorValue {Y : Set X} {d : Data} {CF CT CG CK : ℝ}
    (P : PhysicalPrincipalData Y d CF CT) {y : X} (W : PhysicalPotentialQuarticData P y CG CK)
    (c : I) (a : PhysicalPotentialGeneratorIndex) (u : SphereSobolev (3/2:ℝ)) : SphereSobolev (-(1/2:ℝ)) :=
  ∑ e : PhysicalPotentialGeneratorIndex,normalizedCoordinateGeneratorCoefficients d y a e •
    cubicWordCommutatorValue P W e (modelFirstZeroWordCoefficient d c y) u

/-- The exact cubic comparison survives the fixed-coordinate/radius
normalization. Only genuine old-word lifts and frame VALUES are used. -/
theorem model_first_zero_normalized_word_pair_identity
    {Y : Set X} {d : Data} {CF CT CG CK : ℝ}
    (P : PhysicalPrincipalData Y d CF CT) {y : X} (hy : y ∈ Y) (W : PhysicalPotentialQuarticData P y CG CK)
    (c : I) (a : PhysicalPotentialGeneratorIndex) (u5 : SphereSobolev (5/2:ℝ)) (h : SphereSobolev (3/2:ℝ)) :
    let Z := sphereSobolevInclusionL (1/2:ℝ) 0 (by norm_num);
    let u := sphereSobolevInclusionL (5/2:ℝ) (3/2:ℝ) (by norm_num) u5;
    ⟪Z (framedRaisingHigherL d y (axis c) (scalarModelDegreeSection (fun _ : X => u5) 0)),Z (normalizedPotentialGeneratorHigh P y a h)⟫_ℝ-
      sphereSobolevDualPairing (1/2:ℝ) (modelFirstNormalizedAdjointHigh P W a u) (modelFirstZeroAdjointWeakL d c y h)=
      sphereSobolevDualPairing (1/2:ℝ) (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num) h)
        (modelFirstNormalizedZeroCommutatorValue P W c a u) := by
  have hEach (e : PhysicalPotentialGeneratorIndex) := model_first_zero_raw_word_pair_identity P hy W c e u5 h
  rw [normalized_generator_high_old_words]
  simp only [modelFirstNormalizedAdjointHigh,modelFirstNormalizedZeroCommutatorValue,
    _root_.sum_apply,_root_.smul_apply,map_sum,map_smul,sphereSobolevDualPairing,
    inner_sum,sum_inner,real_inner_smul_left,real_inner_smul_right,←Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro e _
  simpa only [mul_sub,sphereSobolevDualPairing] using
    congrArg (fun t : ℝ => normalizedCoordinateGeneratorCoefficients d y a e*t) (hEach e)

end ShrinkingSpheres.ParallelEnergy
