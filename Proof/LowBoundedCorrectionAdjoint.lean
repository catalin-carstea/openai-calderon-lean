import Proof.GradedGeneratorAdjoints
import Proof.RadialScalarBoundedEndpoints
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped InnerProductSpace
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.DirichletFamily
open OAI.AnisotropicCalderon.SphereHarmonic

lemma sphereSobolevHalfNegativeInclusion_adjoint :
    (sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)).adjoint=
      sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num) := by
  have hL : (sphereSobolevInclusionL 0 (-(1/2:ℝ)) (by norm_num)).comp
      (sphereSobolevInclusionL 1 0 (by norm_num))=
      (sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)).comp
        (sphereSobolevInclusionL 1 (1/2:ℝ) (by norm_num)) := by
    apply ContinuousLinearMap.ext
    intro u
    simp only [ContinuousLinearMap.comp_apply,sphereSobolevInclusionL_trans_apply]
  exact half_endpoint_adjoint_of_coarse_pair _ _ _ _ (fun _ _ => rfl) hL hL

lemma low_bounded_correction_adjoint {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (I0 Zp Zn : E →L[ℝ] E) (hI : I0.adjoint=I0)
    (hZ : I0.comp Zp=Zn.comp I0) : (Zn.comp I0).adjoint=Zp.adjoint.comp I0 := by
  rw [← hZ,ContinuousLinearMap.adjoint_comp,hI]

lemma radialScalarBoundedLow_adjoint (ell : X →L[ℝ] ℝ) (Q : ClosedCoefficientJets 3) :
    ((radialScalarBoundedNegativeL ell Q).comp
      (sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num))).adjoint=
      (radialScalarBoundedHalfL ell Q).adjoint.comp
        (sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)) :=
  low_bounded_correction_adjoint _ _ _ sphereSobolevHalfNegativeInclusion_adjoint
    (radialScalarBounded_half_negative_compatible ell Q)

lemma low_scalar_plus_bounded_adjoint {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (I0 E0 G Gs R Zn Zpa : E →L[ℝ] E)
    (hE : E0=G+Zn.comp I0) (hG : G.adjoint=Gs+R.comp I0)
    (hZ : (Zn.comp I0).adjoint=Zpa.comp I0) :
    E0.adjoint=Gs+(R+Zpa).comp I0 := by
  rw [hE,map_add,hG,hZ,ContinuousLinearMap.add_comp]
  abel
end ShrinkingSpheres
