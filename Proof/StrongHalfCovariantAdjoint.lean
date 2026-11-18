import Proof.StrongHalfCovariantCalculus
import Proof.UniformPhysicalFirstErrorStrongHalf
import Proof.UniformPrincipalModelStrongHalf
import Proof.HalfCovariantAdjointPairing

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
open Set Filter
open scoped ContDiff Topology InnerProductSpace
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.SphereHarmonic

/-- The genuine strong half-domain covariant derivative transports to the
SAME physical adjoint, by weak adjunction and dense inclusion. -/
lemma half_covariant_adjoint_strong_extension (d : Data)
    (C : X → SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ)))
    (H A : X → SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ))
    {y : X} (hC : ContDiffAt ℝ ∞ C y) (b : X)
    (hH : (sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)).comp (H y)=
      (C y).comp (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)))
    (hA : (sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)).comp (A y)=
      (C y).adjoint.comp (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)))
    (L : SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ)))
    (hL : halfOperatorCovariantDerivativeL d C H y b=
      L.comp (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num))) :
    halfOperatorCovariantDerivativeL d (fun x => (C x).adjoint) A y b=
      L.adjoint.comp (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)) := by
  apply ContinuousLinearMap.ext
  intro v
  apply (denseRange_sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)).eq_of_inner_right ℝ
  intro u
  have hPair := half_covariant_adjoint_pairing d C H A hC b hH hA u v
  rw [hL] at hPair
  change ⟪sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num) u,
      halfOperatorCovariantDerivativeL d (fun x => (C x).adjoint) A y b v⟫_ℝ=_
  calc
    _ = ⟪sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num) v,
        L (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num) u)⟫_ℝ := hPair
    _ = _ := ((L.adjoint_inner_right _ _).trans (real_inner_comm _ _)).symm

end ShrinkingSpheres
