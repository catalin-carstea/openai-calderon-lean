import Proof.ParallelNormAssemblyReservedQuadraticPair
import Proof.HalfFamilyDerivativeCalculus
import Proof.EndpointCompatibleDerivative

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2800000
set_option maxRecDepth 10000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter
open scoped ContDiff Topology
namespace ShrinkingSpheres.ParallelEnergy
open OAI.AnisotropicCalderon.SphereHarmonic OAI.AnisotropicCalderon.PrincipalCommutator

/-- The HIGH covariant derivative agrees with the SAME low/HIGH pair's
half covariant derivative on the genuine H5/2 core. Smooth family germs,
endpoint inclusions and connection compatibility are all explicit. -/
lemma higher_covariant_derivative_eq_half (d : Data)
    (C : X → SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ)))
    (H : X → SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ)) (y a : X)
    (hC : ContDiffAt ℝ ∞ C y) (hH : ContDiffAt ℝ ∞ H y)
    (hBalanced : ∀ᶠ x in 𝓝 y,(sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)).comp (H x)=
      (C x).comp (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num))) :
    higherOperatorCovariantDerivativeL d H y a=
      (halfOperatorCovariantDerivativeL d C H y a).comp
        (sphereSobolevInclusionL (5/2:ℝ) (3/2:ℝ) (by norm_num)) := by
  have hAt := hBalanced.self_of_nhds
  have hD := compatible_endpoint_fderiv H C
    (sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num))
    (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)) y a
    (hH.differentiableAt (by simp)) (hC.differentiableAt (by simp)) hBalanced
  rw [halfOperatorCovariantDerivativeL,directional_half_family_comp_fixed C hC a]
  apply ContinuousLinearMap.ext
  intro u
  have hDu := DFunLike.congr_fun hD (sphereSobolevInclusionL (5/2:ℝ) (3/2:ℝ) (by norm_num) u)
  have hB := DFunLike.congr_fun hAt (frameAngularConnectionFiveHalfL d y a u)
  simp only [ContinuousLinearMap.comp_apply] at hDu hB
  rw [frame_connection_five_half_compatible] at hB
  simp only [higherOperatorCovariantDerivativeL,ContinuousLinearMap.comp_apply,_root_.add_apply,
    _root_.sub_apply,directionalFDeriv]
  exact congrArg₂ (fun x z : SphereSobolev (-(1/2:ℝ)) => x+z)
    (congrArg₂ (fun x z : SphereSobolev (-(1/2:ℝ)) => x-z) hDu rfl) hB

/-- Differentiating a HIGH coefficient applied to a genuine H5/2 source
uses only its FIRST actual HIGH coefficient jet and a pointwise genuine
H3/2 lift of the output. This is the left source in the weak Green formula. -/
theorem higher_covariant_apply_to_section (d : Data)
    (H : X → SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ))
    (U : X → SphereSobolev (5/2:ℝ)) (y a : X)
    (hH : ContDiffAt ℝ ∞ H y) (hU : ContDiffAt ℝ ∞ U y)
    (N : SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ))
    (hN : higherOperatorCovariantDerivativeL d H y a=
      (sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)).comp
        (N.comp (sphereSobolevInclusionL (5/2:ℝ) (3/2:ℝ) (by norm_num))))
    (z : SphereSobolev (3/2:ℝ))
    (hz : sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num) z=
      H y (sphereSobolevInclusionL (5/2:ℝ) (3/2:ℝ) (by norm_num) (U y))) :
    fderiv ℝ (fun x => H x (sphereSobolevInclusionL (5/2:ℝ) (3/2:ℝ) (by norm_num) (U x))) y a-
      frameAngularConnectionHigherL d y a z=
      H y (fiveHalfSectionCovariantDerivativeL d U y a)+
        N (sphereSobolevInclusionL (5/2:ℝ) (3/2:ℝ) (by norm_num) (U y)) := by
  let K := sphereSobolevInclusionL (5/2:ℝ) (3/2:ℝ) (by norm_num)
  have hKU := K.hasFDerivAt.comp y (hU.differentiableAt (by simp)).hasFDerivAt
  have hProduct := ((hH.differentiableAt (by simp)).hasFDerivAt.clm_apply hKU).fderiv
  have hD : fderiv ℝ (fun x => H x (K (U x))) y a=
      H y (K (fderiv ℝ U y a))+(fderiv ℝ H y a) (K (U y)) := by
    simpa only [ContinuousLinearMap.comp_apply,_root_.add_apply,ContinuousLinearMap.flip_apply,Function.comp_apply] using
      congrArg (fun A : X →L[ℝ] SphereSobolev (1/2:ℝ) => A a) hProduct
  have hRaw := DFunLike.congr_fun hN (U y)
  simp only [higherOperatorCovariantDerivativeL,ContinuousLinearMap.comp_apply,_root_.add_apply,_root_.sub_apply] at hRaw
  have hRot := DFunLike.congr_fun (frameAngularConnectionHigherL_compatible d y a) z
  simp only [ContinuousLinearMap.comp_apply] at hRot
  rw [hz] at hRot
  have hCoe : (fderiv ℝ H y a) (K (U y))-frameAngularConnectionHigherL d y a z+
      H y (frameAngularConnectionFiveHalfL d y a (U y))=N (K (U y)) := by
    apply sphereSobolevInclusionL_injective (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)
    simp only [map_add,map_sub]
    rw [←hRot] at hRaw
    exact hRaw
  rw [hD]
  simp only [fiveHalfSectionCovariantDerivativeL,map_sub]
  dsimp only [K] at hCoe ⊢
  have hAdd := congrArg (fun v => v+H y (sphereSobolevInclusionL (5/2:ℝ) (3/2:ℝ) (by norm_num) (fderiv ℝ U y a))-
    H y (frameAngularConnectionFiveHalfL d y a (U y))) hCoe
  convert hAdd using 1 <;> abel

end ShrinkingSpheres.ParallelEnergy
