import Proof.ReflectedFirstCorrectionAdjoint
import Proof.PhysicalPotentialFirstWordLifts
import Proof.PhysicalFirstAdjointHigherFamily

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.SphereHarmonic

def PhysicalPrincipalData.firstDerivativeAdjointFiveHalfL
    {Y : Set X} {d : Data} {CF CT CG CK : ℝ} (P : PhysicalPrincipalData Y d CF CT)
    {y : X} (W : PhysicalPotentialQuarticData P y CG CK) (j : I) :
    SphereSobolev (5/2:ℝ) →L[ℝ] SphereSobolev (3/2:ℝ) :=
  ((∑ i : I,((frameTensorMatrix d.γ d.frame y (principal d.γ d.g₂ y) i j+
      frameTensorMatrix d.γ d.frame y (principal d.γ d.g₂ y) j i)*
      scaledFrameLogRadius d.radius d.frame i y) • W.reverseFirstWordHigherL (.inl ()))+
    (2:ℝ) • (∑ i : I,(frameTensorMatrix d.γ d.frame y (principal d.γ d.g₂ y) i j-
      (if i=j then 1 else 0)) • W.reverseFirstWordHigherL (.inr (.inl i))))+
    d.radius y • (∑ i : I,(frameTensorMatrix d.γ d.frame y (principal d.γ d.g₂ y) i j+
      frameTensorMatrix d.γ d.frame y (principal d.γ d.g₂ y) j i) •
      (firstFrameCorrectionAdjointFiveHalfL d y i+W.reverseFirstWordHigherL (.inr (.inr i))))

/-- A genuine common-domain lift of the complete SAME full first adjoint.
Every model, bounded-correction and actual-error term is retained. -/
lemma PhysicalPrincipalData.firstDerivativeAdjointFiveHalfL_inclusion
    {Y : Set X} {d : Data} {CF CT CG CK : ℝ} (P : PhysicalPrincipalData Y d CF CT)
    {y : X} (hy : y ∈ Y) (W : PhysicalPotentialQuarticData P y CG CK) (j : I) :
    (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)).comp
      (P.firstDerivativeAdjointFiveHalfL W j)=
      (P.firstDerivativeAdjointHigherFamily (fun i => W.adjointHigh (.inr (.inl i)))
        (fun i _ => W.adjointHigh (.inr (.inr i))) y j).comp
          (sphereSobolevInclusionL (5/2:ℝ) (3/2:ℝ) (by norm_num)) := by
  apply ContinuousLinearMap.ext
  intro u
  have hDeg := W.reverseFirstWordHigherL_inclusion (.inl ()) u
  rw [W.adjointHigh_degree hy] at hDeg
  change sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)
      (W.reverseFirstWordHigherL (.inl ()) u)=
      degreeHigherL (sphereSobolevInclusionL (5/2:ℝ) (3/2:ℝ) (by norm_num) u) at hDeg
  have hR (i : I) := W.reverseFirstWordHigherL_inclusion (.inr (.inl i)) u
  have hE (i : I) := W.reverseFirstWordHigherL_inclusion (.inr (.inr i)) u
  have hC (i : I) := DFunLike.congr_fun (firstFrameCorrectionAdjointFiveHalfL_inclusion d y i) u
  simp only [ContinuousLinearMap.comp_apply] at hC
  simp only [PhysicalPrincipalData.firstDerivativeAdjointFiveHalfL,
    PhysicalPrincipalData.firstDerivativeAdjointHigherFamily,ContinuousLinearMap.comp_apply,
    _root_.add_apply,_root_.sum_apply,_root_.smul_apply,map_add,map_sum,map_smul,hDeg,hR,hE,hC]

end ShrinkingSpheres
