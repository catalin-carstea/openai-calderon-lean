import Proof.BasicRadialAngularPackets
import Proof.CoarseAngularFieldBudgets
import Proof.CoarseAngularFieldSmoothness
import Proof.RotationFirstCorrectionDerivative
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped BigOperators ContDiff
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.DirichletFamily
open OAI.AnisotropicCalderon.SphereHarmonic OAI.AnisotropicCalderon.SmoothSphereRotation

def rotationCovectorMapL (i j : I) : (X →L[ℝ] ℝ) →L[ℝ] (X →L[ℝ] ℝ) :=
  (ContinuousLinearMap.compL ℝ X X ℝ).flip (rotationVectorL i j)

lemma rotationCovectorMapL_apply (i j : I) (q : X →L[ℝ] ℝ) :
    rotationCovectorMapL i j q = rotationCovector q i j := by
  apply ContinuousLinearMap.ext
  intro z
  simp only [rotationCovectorMapL,ContinuousLinearMap.flip_apply,ContinuousLinearMap.compL_apply,ContinuousLinearMap.comp_apply,
    rotationCovector,rotationVectorL_apply,rotationVector,map_sub,map_smul,_root_.sub_apply,
    _root_.smul_apply,PiLp.proj_apply,smul_eq_mul,axis]
  ring

def firstRadialForwardOperatorMapL : (X →L[ℝ] ℝ) →L[ℝ] (SphereSobolev 1 →L[ℝ] SphereSobolev 0) :=
  ((ContinuousLinearMap.compL ℝ (SphereSobolev 1) (SphereSobolev 0) (SphereSobolev 0)).flip
    (sphereSobolevInclusionL 1 0 (by norm_num))).comp radialCorrectionCovectorL

def firstRadialAdjointOperatorMapL : (X →L[ℝ] ℝ) →L[ℝ] (SphereSobolev 1 →L[ℝ] SphereSobolev 0) :=
  ((ContinuousLinearMap.compL ℝ (SphereSobolev 1) (SphereSobolev 0) (SphereSobolev 0)).flip
    (sphereSobolevInclusionL 1 0 (by norm_num))).comp
      ((ContinuousLinearMap.adjoint : (SphereSobolev 0 →L[ℝ] SphereSobolev 0) ≃ₗᵢ[ℝ]
        (SphereSobolev 0 →L[ℝ] SphereSobolev 0)).toContinuousLinearEquiv.toContinuousLinearMap.comp radialCorrectionCovectorL)

lemma firstRadialForwardOperatorMapL_apply (q : X →L[ℝ] ℝ) :
    firstRadialForwardOperatorMapL q = (radialCorrectionCovectorL q).comp
      (sphereSobolevInclusionL 1 0 (by norm_num)) := rfl
lemma firstRadialAdjointOperatorMapL_apply (q : X →L[ℝ] ℝ) :
    firstRadialAdjointOperatorMapL q = (radialCorrectionCovectorL q).adjoint.comp
      (sphereSobolevInclusionL 1 0 (by norm_num)) := rfl

def firstRadialAngularFieldJetBudget : ℝ :=
  ‖firstRadialAdjointOperatorMapL‖+‖firstRadialForwardOperatorMapL‖+
    (∑ ij : I × I,‖firstRadialAdjointOperatorMapL.comp (rotationCovectorMapL ij.1 ij.2)‖)+
    (∑ ij : I × I,‖firstRadialForwardOperatorMapL.comp (rotationCovectorMapL ij.1 ij.2)‖)
lemma firstRadialAngularFieldJetBudget_nonneg : 0 ≤ firstRadialAngularFieldJetBudget := by
  unfold firstRadialAngularFieldJetBudget
  positivity

lemma firstRadialAdjointFields_jet_bound
    {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    {ell : P → X →L[ℝ] ℝ} {p : P} {N : ℕ} {B : ℝ}
    (hEll : SmoothFiniteJetBound ell p N B) :
    CoarseAngularFields.JetBound (fun x => CoarseAngularFields.ofPacket (firstRadialAdjointCoarsePacket (ell x)))
      p N (firstRadialAngularFieldJetBudget*B) := by
  obtain ⟨h1,h2,h3,h4⟩ := four_block_budget_bounds
    ‖firstRadialAdjointOperatorMapL‖ ‖firstRadialForwardOperatorMapL‖
    (fun ij => ‖firstRadialAdjointOperatorMapL.comp (rotationCovectorMapL ij.1 ij.2)‖)
    (fun ij => ‖firstRadialForwardOperatorMapL.comp (rotationCovectorMapL ij.1 ij.2)‖)
    (norm_nonneg _) (norm_nonneg _) (fun _ => norm_nonneg _) (fun _ => norm_nonneg _)
  refine ⟨(hEll.clm firstRadialAdjointOperatorMapL).weaken (mul_le_mul_of_nonneg_right h1 hEll.nonneg),
    (hEll.clm firstRadialForwardOperatorMapL).weaken (mul_le_mul_of_nonneg_right h2 hEll.nonneg),?_,?_⟩
  · intro ij
    have hh := (hEll.clm (firstRadialAdjointOperatorMapL.comp (rotationCovectorMapL ij.1 ij.2))).weaken
      (mul_le_mul_of_nonneg_right (h3 ij) hEll.nonneg)
    simpa only [firstRadialAngularFieldJetBudget,firstRadialAdjointOperatorMapL_apply,Function.comp_def,ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.flip_apply,ContinuousLinearMap.compL_apply,rotationCovectorMapL_apply,CoarseAngularFields.ofPacket,
      firstRadialAdjointCoarsePacket] using hh
  · intro ij
    have hh := (hEll.clm (firstRadialForwardOperatorMapL.comp (rotationCovectorMapL ij.1 ij.2))).weaken
      (mul_le_mul_of_nonneg_right (h4 ij) hEll.nonneg)
    simpa only [firstRadialAngularFieldJetBudget,firstRadialForwardOperatorMapL_apply,Function.comp_def,ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.flip_apply,ContinuousLinearMap.compL_apply,rotationCovectorMapL_apply,CoarseAngularFields.ofPacket,
      firstRadialAdjointCoarsePacket] using hh

lemma firstRadialAdjointFields_smoothAt
    {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    {ell : P → X →L[ℝ] ℝ} {p : P} (hEll : ContDiffAt ℝ ∞ ell p) :
    CoarseAngularFields.SmoothAt (fun x => CoarseAngularFields.ofPacket (firstRadialAdjointCoarsePacket (ell x))) p := by
  refine ⟨firstRadialAdjointOperatorMapL.contDiff.contDiffAt.comp p hEll,
    firstRadialForwardOperatorMapL.contDiff.contDiffAt.comp p hEll,?_,?_⟩
  · intro ij
    have hh := (firstRadialAdjointOperatorMapL.comp (rotationCovectorMapL ij.1 ij.2)).contDiff.contDiffAt.comp p hEll
    simpa only [firstRadialAngularFieldJetBudget,firstRadialAdjointOperatorMapL_apply,Function.comp_def,ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.flip_apply,ContinuousLinearMap.compL_apply,rotationCovectorMapL_apply,CoarseAngularFields.ofPacket,
      firstRadialAdjointCoarsePacket] using hh
  · intro ij
    have hh := (firstRadialForwardOperatorMapL.comp (rotationCovectorMapL ij.1 ij.2)).contDiff.contDiffAt.comp p hEll
    simpa only [firstRadialAngularFieldJetBudget,firstRadialForwardOperatorMapL_apply,Function.comp_def,ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.flip_apply,ContinuousLinearMap.compL_apply,rotationCovectorMapL_apply,CoarseAngularFields.ofPacket,
      firstRadialAdjointCoarsePacket] using hh
end ShrinkingSpheres
