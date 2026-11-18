import Proof.HalfRotationDistribution
import Proof.GradedGeneratorAdjoints
import Proof.LowBoundedCorrectionAdjoint
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped InnerProductSpace
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.SphereHarmonic

/-- The true dual-half adjoint retains the SAME rotation graph with the
true adjoint of its rotation commutator. All endpoint inclusions are explicit. -/
lemma half_rotation_distribution_adjoint (i j : I)
    (A C : SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ)))
    (hGraph : ∀ u : SphereSobolev (3/2:ℝ),
      sphereSobolevInclusionL (-(1/2:ℝ)) (-(3/2:ℝ)) (by norm_num)
        (A (sphereSobolevRotationL (3/2:ℝ) i j u)+
          C (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num) u))=
      sphereSobolevRotationL (-(1/2:ℝ)) i j
        (A (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num) u)))
    (u : SphereSobolev (3/2:ℝ)) :
    sphereSobolevInclusionL (-(1/2:ℝ)) (-(3/2:ℝ)) (by norm_num)
      (A.adjoint (sphereSobolevRotationL (3/2:ℝ) i j u)+
        C.adjoint (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num) u))=
      sphereSobolevRotationL (-(1/2:ℝ)) i j
        (A.adjoint (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num) u)) := by
  let I0 := sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)
  let R0 := sphereSobolevRotationL (1/2:ℝ) i j
  have hIhi : sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)=I0 := by
    unfold sphereSobolevInclusionL I0
    congr 1 <;> norm_num
  have hIlo : sphereSobolevInclusionL (-(1/2:ℝ)) (-(3/2:ℝ)) (by norm_num)=I0 := by
    unfold sphereSobolevInclusionL I0
    congr 1 <;> norm_num
  have hRhi : sphereSobolevRotationL (3/2:ℝ) i j=R0 := rfl
  have hRlo : sphereSobolevRotationL (-(1/2:ℝ)) i j=R0 := rfl
  have hOp : I0.comp (A.comp R0+C.comp I0)=R0.comp (A.comp I0) := by
    apply ContinuousLinearMap.ext
    intro v
    simpa only [ContinuousLinearMap.comp_apply,_root_.add_apply,hIhi,hIlo,hRhi,hRlo] using hGraph v
  have hAdj := congrArg (fun T : SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ)) => T.adjoint) hOp
  have hIA : I0.adjoint=I0 := sphereSobolevHalfNegativeInclusion_adjoint
  have hRA : R0.adjoint= -R0 := sphereSobolevRotationHalf_adjoint i j
  simp only [ContinuousLinearMap.adjoint_comp,map_add,hIA,hRA,ContinuousLinearMap.add_comp,
    ContinuousLinearMap.comp_add,ContinuousLinearMap.neg_comp,ContinuousLinearMap.comp_neg,
    ContinuousLinearMap.comp_assoc] at hAdj
  have hNew : I0.comp (A.adjoint.comp R0+C.adjoint.comp I0)=R0.comp (A.adjoint.comp I0) := by
    simp only [ContinuousLinearMap.comp_add,ContinuousLinearMap.comp_assoc]
    let X0 := R0.comp (A.adjoint.comp I0)
    let Y0 := I0.comp (A.adjoint.comp R0)
    let Z0 := I0.comp (C.adjoint.comp I0)
    change -X0+Z0= -Y0 at hAdj
    change Y0+Z0=X0
    have hh : Z0-X0= -Y0 := (show Z0-X0= -X0+Z0 by abel).trans hAdj
    have hZ : Z0= -Y0+X0 := eq_add_of_sub_eq hh
    rw [hZ]
    abel
  simpa only [ContinuousLinearMap.comp_apply,_root_.add_apply,hIhi,hIlo,hRhi,hRlo] using DFunLike.congr_fun hNew u
end ShrinkingSpheres
