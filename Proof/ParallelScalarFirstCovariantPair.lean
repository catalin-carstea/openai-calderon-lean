import Proof.CovariantHalfOperatorMixedGreen
import Proof.HalfCanonicalCovariantSection

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2600000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
open Set Filter
open scoped ContDiff Topology InnerProductSpace
namespace ShrinkingSpheres.ParallelEnergy
open OAI.AnisotropicCalderon.SphereHarmonic

/-- Pointwise Leibniz identity for a genuine half-order coefficient pair.
The two angular frame-connection terms cancel by their actual adjunction
and compatibility graphs, before a norm is taken. -/
theorem half_covariant_pair_fderiv (d : Data)
    (C : X → SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ)))
    (Ch : X → SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ))
    (U V : X → SphereSobolev (3/2:ℝ)) (y a : X)
    (hC : ContDiffAt ℝ ∞ C y) (hU : ContDiffAt ℝ ∞ U y) (hV : ContDiffAt ℝ ∞ V y)
    (hCh : (sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)).comp (Ch y)=
      (C y).comp (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num))) :
    let J := sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)
    fderiv ℝ (fun x => sphereSobolevDualPairing (1/2:ℝ) (J (U x)) (C x (J (V x)))) y a=
      sphereSobolevDualPairing (1/2:ℝ) (halfSectionCovariantDerivativeL d U y a) (C y (J (V y)))+
      sphereSobolevDualPairing (1/2:ℝ) (J (U y)) (C y (halfSectionCovariantDerivativeL d V y a))+
      sphereSobolevDualPairing (1/2:ℝ) (J (U y)) (halfOperatorCovariantDerivativeL d C Ch y a (V y)) := by
  let J := sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)
  let C0 := fun x => (C x).comp J
  have hC0 : ContDiffAt ℝ ∞ C0 y := hC.clm_comp contDiffAt_const
  have hJU := J.hasFDerivAt.comp y (hU.differentiableAt (by simp)).hasFDerivAt
  have hCV := (hC0.differentiableAt (by simp)).hasFDerivAt.clm_apply
    (hV.differentiableAt (by simp)).hasFDerivAt
  have hRaw := fderiv_inner_apply ℝ hJU.differentiableAt hCV.differentiableAt a
  rw [hJU.fderiv,hCV.fderiv] at hRaw
  have hCancel := graded_connection_first_integrand_mixed
    (sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num))
    (frameAngularConnectionHalfL d y a) (C y) J (Ch y)
    (frameAngularConnectionHigherL d y a)
    (fderiv ℝ C0 y a) (halfOperatorCovariantDerivativeL d C Ch y a)
    sphereSobolevHalfNegativeInclusion_adjoint (frameAngularConnectionHalfL_adjoint d y a)
    hCh (frameAngularConnectionHigherL_compatible d y a) rfl (U y) (V y) (fderiv ℝ U y a)
  dsimp only [sphereSobolevDualPairing] at hRaw hCancel ⊢
  simp only [ContinuousLinearMap.comp_apply,_root_.add_apply,
    ContinuousLinearMap.flip_apply,inner_add_right,Function.comp_apply] at hRaw
  simp only [halfSectionCovariantDerivativeL_apply,map_sub,inner_sub_right]
  change fderiv ℝ (fun x => ⟪J (U x),C0 x (V x)⟫_ℝ) y a=_ at hRaw
  change fderiv ℝ (fun x => ⟪J (U x),C0 x (V x)⟫_ℝ) y a=_
  dsimp only [J,C0] at hRaw hCancel ⊢
  simp only [ContinuousLinearMap.comp_apply] at hRaw ⊢
  linarith only [hRaw,hCancel]

/-- Triple reduction for an arbitrary symmetric bilinear pairing. Its
curvature terms are retained explicitly; no connection coefficient is
estimated in isolation. -/
lemma symmetric_pair_second_triple_algebra {E A : Type*} [AddCommGroup E]
    (B : E → E → ℝ) (hB : ∀ u v,B u v=B v u)
    (hSub : ∀ u v w,B (u-v) w=B u w-B v w)
    (V : A → E) (H R : A → A → E)
    (hR : ∀ a b,H a b-H b a=R a b) (a b c : A) :
    2*B (H a b) (V c)=
      (B (H a b) (V c)+B (V b) (H a c))+
      (B (H b a) (V c)+B (V a) (H b c))-
      (B (H c a) (V b)+B (V a) (H c b))+
      B (R a b) (V c)+B (R c b) (V a)-B (R a c) (V b) := by
  have hab := congrArg (fun t => B t (V c)) (hR a b)
  have hcb := congrArg (fun t => B t (V a)) (hR c b)
  have hac := congrArg (fun t => B t (V b)) (hR a c)
  simp only [hSub] at hab hcb hac
  rw [hB (V b),hB (V a),hB (V a)]
  linarith only [hab,hcb,hac]

end ShrinkingSpheres.ParallelEnergy
