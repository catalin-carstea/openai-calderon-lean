import Proof.HalfCovariantScalarProduct
import Proof.FrameCoordinateCovectors
import Proof.FrameErrorMatrixRaisingCross
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
open Set
open scoped ContDiff Topology
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.SphereHarmonic

/-- The literal half-order covariant operator derivative is linear in its
    physical direction, with the same actual coefficient families. -/
def halfOperatorCovariantDerivativeFamilyL (d : Data)
    (C : X → SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ)))
    (Ch : X → SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ)) (y : X) :
    X →L[ℝ] (SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ))) :=
  fderiv ℝ (fun x => (C x).comp (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num))) y-
    ∑ i : I,∑ j : I,((1/2:ℝ) • frameConnectionLinear d.γ d.frame y i j).smulRight
      ((sphereSobolevRotationL (1/2:ℝ) i j).comp (Ch y)-
        (C y).comp (sphereSobolevRotationL (3/2:ℝ) i j))

lemma halfOperatorCovariantDerivativeFamilyL_apply (d : Data)
    (C : X → SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ)))
    (Ch : X → SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ)) (y a : X) :
    halfOperatorCovariantDerivativeFamilyL d C Ch y a=halfOperatorCovariantDerivativeL d C Ch y a := by
  apply ContinuousLinearMap.ext
  intro u
  simp only [halfOperatorCovariantDerivativeFamilyL,halfOperatorCovariantDerivativeL,
    OAI.AnisotropicCalderon.PrincipalCommutator.directionalFDeriv,
    frameAngularConnectionHalfL,frameAngularConnectionHigherL,
    ContinuousLinearMap.comp_apply,ContinuousLinearMap.smulRight_apply,
    _root_.sub_apply,_root_.add_apply,_root_.sum_apply,_root_.smul_apply,
    frameConnectionLinear_apply,smul_eq_mul,map_sum,map_smul,smul_sub]
  simp only [Fin.sum_univ_three]
  module

lemma norm_linear_axis_le_three_frame_bound {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {Y : Set X} {g : MetricField} {K : ℝ} (hg : Elliptic Y K g) (hK : 1 ≤ K)
    (e : Frame) {y : X} (hy : y ∈ Y)
    (hFrame : ∀ j k,metricPair g y (e y j) (e y k)=if j=k then 1 else 0)
    (V : X →L[ℝ] F) (Q : ℝ) (hV : ∀ j,‖V (e y j)‖ ≤ Q) (i : I) :
    ‖V (axis i)‖ ≤ 3*K*Q := by
  have hEq : V (axis i)=∑ j : I,frameCoordinateLinear g e y j (axis i) • V (e y j) := by
    have hh := congrArg V (frameCoordinateLinear_reconstruct g e y (axis i) hFrame)
    simpa only [map_sum,map_smul] using hh.symm
  rw [hEq]
  exact norm_weighted_sum_three_le _ _ K Q (zero_le_one.trans hK)
    (fun j => by
      rw [frameCoordinateLinear_apply]
      exact hg.frame_coordinate_abs_bound hK e hy hFrame i j) hV

lemma norm_halfOperatorCovariantDerivativeL_axis_le {Y : Set X} (d : Data)
    {K : ℝ} (hg : Elliptic Y K d.γ) (hK : 1 ≤ K) {y : X} (hy : y ∈ Y)
    (hFrame : ∀ j k,metricPair d.γ y (d.frame y j) (d.frame y k)=if j=k then 1 else 0)
    (C : X → SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ)))
    (Ch : X → SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ))
    (Q : ℝ) (hD : ∀ j,‖halfOperatorCovariantDerivativeL d C Ch y (d.frame y j)‖ ≤ Q) (i : I) :
    ‖halfOperatorCovariantDerivativeL d C Ch y (axis i)‖ ≤ 3*K*Q := by
  rw [← halfOperatorCovariantDerivativeFamilyL_apply]
  exact norm_linear_axis_le_three_frame_bound hg hK d.frame hy hFrame
    (halfOperatorCovariantDerivativeFamilyL d C Ch y) Q
    (fun j => by rw [halfOperatorCovariantDerivativeFamilyL_apply];exact hD j) i
end ShrinkingSpheres
