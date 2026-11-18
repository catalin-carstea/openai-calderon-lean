import Proof.GradedConnectionPairing
import Proof.LowBoundedCorrectionAdjoint
import Proof.RightMultiplierRotationGraph
import Proof.MetricSmooth
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
open scoped ContDiff Topology InnerProductSpace
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.SphereHarmonic

def frameAngularConnectionHalfL (d : Data) (y a : X) :
    SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ)) :=
  ∑ i : I,∑ j : I,((1/2:ℝ)*frameConnectionCoefficient d.γ d.frame y a i j) • sphereSobolevRotationL (1/2:ℝ) i j

def frameAngularConnectionHigherL (d : Data) (y a : X) :
    SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ) :=
  ∑ i : I,∑ j : I,((1/2:ℝ)*frameConnectionCoefficient d.γ d.frame y a i j) • sphereSobolevRotationL (3/2:ℝ) i j

lemma frameAngularConnectionHalfL_adjoint (d : Data) (y a : X) :
    (frameAngularConnectionHalfL d y a).adjoint= -frameAngularConnectionHalfL d y a := by
  simp only [frameAngularConnectionHalfL,map_sum,map_smul,sphereSobolevRotationHalf_adjoint,
    smul_neg,Finset.sum_neg_distrib]

lemma contDiffOn_frameAngularConnectionHigherL {Y : Set X} (hY : IsOpen Y)
    (d : Data) {K : ℝ} (hg : Elliptic Y K d.γ) (hK : 0 < K)
    (he : ∀ i,ContDiffOn ℝ ∞ (fun x => d.frame x i) Y) (a : X) :
    ContDiffOn ℝ ∞ (fun x => frameAngularConnectionHigherL d x a) Y := by
  exact ContDiffOn.sum (fun i _ => ContDiffOn.sum (fun j _ =>
    (contDiffOn_const.mul (hg.contDiffOn_frameConnection hY hK d.frame he
      (fun _ => a) contDiffOn_const i j)).smul contDiffOn_const))

lemma frameAngularConnectionHigherL_compatible (d : Data) (y a : X) :
    (sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)).comp (frameAngularConnectionHigherL d y a)=
      (frameAngularConnectionHalfL d y a).comp (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)) := by
  apply ContinuousLinearMap.ext
  intro u
  simp only [frameAngularConnectionHalfL,frameAngularConnectionHigherL,ContinuousLinearMap.comp_apply,
    _root_.sum_apply,_root_.smul_apply,map_sum,map_smul]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  congr 1
  simpa only [sphereSobolevInclusionL,show (3/2:ℝ)-1=1/2 by norm_num,show (1/2:ℝ)-1= -(1/2:ℝ) by norm_num] using
    (sphereSobolevRotationL_inclusion_apply (3/2:ℝ) (1/2:ℝ) (by norm_num) i j u).symm

/-- Actual frame connection terms cancel for the SAME compatible coefficient
    endpoints; no bound on derivatives of the chosen frame is required. -/
lemma frame_connection_pair_cancel (d : Data) (y a : X)
    (C : SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ)))
    (Ch : SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ))
    (hCh : (sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)).comp Ch=
      C.comp (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)))
    (u : SphereSobolev (3/2:ℝ)) :
    sphereSobolevDualPairing (1/2:ℝ) (frameAngularConnectionHigherL d y a u)
      (C (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num) u))+
    sphereSobolevDualPairing (1/2:ℝ) (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num) u)
      (frameAngularConnectionHalfL d y a (Ch u))=0 :=
  graded_connection_pair_cancel _ _ _ _ _ _ sphereSobolevHalfNegativeInclusion_adjoint
    (frameAngularConnectionHalfL_adjoint d y a) hCh (frameAngularConnectionHigherL_compatible d y a) u
end ShrinkingSpheres
