import Proof.BoundaryGradientCoefficientLocality
import Proof.RelativeCenterErrorCoefficientFamily
import Proof.NormalFrameRelativeActualParameter
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
open Set Filter
open scoped ContDiff Topology
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.DirichletFamily
open OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open OAI.AnisotropicCalderon.SphereHarmonic

def actualCenterErrorWeight (d : Data) (x a : X) (j : I) (z : X) : ℝ :=
  metricPair d.γ x ((normalizedParallelCenterJacobian d.γ d.expMap x
    (d.radius x • frameVector d.frame x z)-ContinuousLinearMap.id ℝ X) a) (d.frame x j)

def RealizesActualCenterGradientAdjoint (d : Data) (x a : X)
    (A G : SphereSobolev 1 →L[ℝ] SphereSobolev 0) : Prop :=
  ∀ W : I → SmoothCoefficientJets 2,
    (∀ j : I,∀ w : UnitSphere,coefficientValue 2 (W j) w.val = actualCenterErrorWeight d x a j w.val) →
    G = (d.radius x)⁻¹ • boundaryGradientAdjointL W A

lemma realizesActualCenterGradientAdjoint_of_coefficients (d : Data) (x a : X)
    (A : SphereSobolev 1 →L[ℝ] SphereSobolev 0) (W : I → SmoothCoefficientJets 2)
    (hW : ∀ j : I,∀ w : UnitSphere,coefficientValue 2 (W j) w.val = actualCenterErrorWeight d x a j w.val) :
    RealizesActualCenterGradientAdjoint d x a A ((d.radius x)⁻¹ • boundaryGradientAdjointL W A) := by
  intro V hV
  apply congrArg (fun T : SphereSobolev 1 →L[ℝ] SphereSobolev 0 => (d.radius x)⁻¹ • T)
  exact (boundaryGradientL_and_adjoint_congr_sphere W V
    (fun j w => (hW j w).trans (hV j w).symm) A A).2

lemma RealizesActualCenterGradientAdjoint.unique (d : Data) (x a : X)
    (A G H : SphereSobolev 1 →L[ℝ] SphereSobolev 0)
    (hG : RealizesActualCenterGradientAdjoint d x a A G)
    (hH : RealizesActualCenterGradientAdjoint d x a A H)
    (W : I → SmoothCoefficientJets 2)
    (hW : ∀ j : I,∀ w : UnitSphere,coefficientValue 2 (W j) w.val = actualCenterErrorWeight d x a j w.val) : G = H :=
  (hG W hW).trans (hH W hW).symm

namespace RelativeCenterErrorCoefficientFamily
variable {d : Data} {y a : X} {j : I} {CC CH : ℝ}

def atParameterCoefficient (C : RelativeCenterErrorCoefficientFamily d y a j CC CH)
    (p : NormalFrameRelativeParameter) : SmoothCoefficientJets 2 :=
  smoothMultiplierLowerJets (commonSupportCoefficientFamily 3 C.scalar C.smooth C.support C.compact C.supported p)

lemma atParameterCoefficient_actual (C : RelativeCenterErrorCoefficientFamily d y a j CC CH)
    (hr : d.radius y ≠ 0) (x : X)
    (hp : normalFrameRelativeActualParameter d (d.radius y) x ∈ C.domain)
    (w : UnitSphere) :
    coefficientValue 2 (C.atParameterCoefficient (normalFrameRelativeActualParameter d (d.radius y) x)) w.val =
      actualCenterErrorWeight d x a j w.val := by
  have hw2 : w.val ∈ Metric.closedBall (0:X) 2 :=
    Metric.closedBall_subset_closedBall (by norm_num) (Metric.sphere_subset_closedBall w.property)
  rw [atParameterCoefficient,coefficientValue_smoothMultiplierLowerJets,
    coefficientValue_commonSupportCoefficientFamily]
  rw [(C.actual _ hp w.val hw2).eq_of_nhds]
  have hRadius : (1+(d.radius x/d.radius y-1))*d.radius y = d.radius x := by field_simp;ring
  simp only [normalFrameRelativeCenterErrorWeight,normalFrameRelativeParallelCenterError,
    normalFrameRelativeRadiusInput,normalFrameRelativeActualParameter,normalFrameRadialParallelCenter,
    Function.comp_apply,normalFrameParallelCenterJacobian,normalFrameRadialReorderL_apply,
    normalFrameInput,frameVectorLinear_apply,frameVector_axis,actualCenterErrorWeight]
  rw [hRadius]
end RelativeCenterErrorCoefficientFamily
end ShrinkingSpheres
