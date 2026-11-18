import Proof.HalfCanonicalCovariantSection
import Proof.CovariantHalfOperatorGreen

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
open scoped ContDiff Topology
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.SphereHarmonic OAI.AnisotropicCalderon.PrincipalCommutator

/-- The actual covariant coefficient/source Leibniz rule at the balanced
endpoints. The companion higher family occurs in the SAME connection term
on both sides; a caller supplies its genuine graph for adjunction. -/
lemma half_covariant_operator_source_product (d : Data)
    (C : X → SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ)))
    (Ch : X → SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ))
    (U : X → SphereSobolev (3/2:ℝ)) (y a : X)
    (hC : ContDiffAt ℝ ∞ C y) (hU : ContDiffAt ℝ ∞ U y) :
    fderiv ℝ (fun x => C x (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num) (U x))) y a-
      frameAngularConnectionHalfL d y a (Ch y (U y))=
      C y (halfSectionCovariantDerivativeL d U y a)+
        halfOperatorCovariantDerivativeL d C Ch y a (U y) := by
  let J := sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)
  let B := fun x => (C x).comp J
  have hB := hC.clm_comp (contDiffAt_const : ContDiffAt ℝ ∞ (fun _ : X => J) y)
  have hApp : fderiv ℝ (fun x => B x (U x)) y a=
      (fderiv ℝ B y a) (U y)+C y (J (fderiv ℝ U y a)) := by
    rw [fderiv_clm_apply (hB.differentiableAt (by simp)) (hU.differentiableAt (by simp))]
    simp only [ContinuousLinearMap.add_apply,ContinuousLinearMap.comp_apply,ContinuousLinearMap.flip_apply]
    exact add_comm _ _
  change fderiv ℝ (fun x => B x (U x)) y a-frameAngularConnectionHalfL d y a (Ch y (U y))=_
  rw [hApp,halfSectionCovariantDerivativeL_apply]
  simp only [halfOperatorCovariantDerivativeL,ContinuousLinearMap.comp_apply,_root_.add_apply,_root_.sub_apply,
    directionalFDeriv,map_sub]
  change (fderiv ℝ B y a) (U y)+C y (J (fderiv ℝ U y a))-
    frameAngularConnectionHalfL d y a (Ch y (U y))=
      (C y (J (fderiv ℝ U y a))-C y (frameAngularConnectionHigherL d y a (U y)))+
        ((fderiv ℝ B y a) (U y)-frameAngularConnectionHalfL d y a (Ch y (U y))+
          C y (frameAngularConnectionHigherL d y a (U y)))
  abel

end ShrinkingSpheres
