import Proof.FirstErrorCoordinateContraction
import Proof.PrincipalFirstErrorCoordinateWeights

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
open Set
open scoped ContDiff Topology
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.SphereHarmonic

def principalFirstErrorCoordinateCoarseL (d : Data)
    (A : X → SphereSobolev 1 →L[ℝ] SphereSobolev 0)
    (G : I → X → SphereSobolev 1 →L[ℝ] SphereSobolev 0) (b : I) (x : X) :
    SphereSobolev 1 →L[ℝ] SphereSobolev 0 :=
  ∑ a : I,principalFirstErrorCoordinateWeight d a b x •
    actualFirstAdjointErrorFamily d (axis a) A (G a) x

/-- The coordinate coarse family represents the SAME actual physical
first-error coefficient across its genuine Sobolev inclusion graph. -/
lemma PhysicalPrincipalData.first_error_coordinate_coarse_compatible
    {Y : Set X} {d : Data} {CF CT : ℝ} (P : PhysicalPrincipalData Y d CF CT)
    {x : X} (hx : x ∈ Y)
    (hFrame : ∀ i j,metricPair d.γ x (d.frame x i) (d.frame x j)=if i=j then 1 else 0)
    (b : I) :
    (sphereSobolevInclusionL 0 (-(1/2:ℝ)) (by norm_num)).comp
      (principalFirstErrorCoordinateCoarseL d P.adjoint P.center b x)=
      (P.first.principalFirstErrorCoordinateHalfL x b).comp
        (sphereSobolevInclusionL 1 (1/2:ℝ) (by norm_num)) := by
  have hTensor := frameTensor_operator_coordinate_contraction d.γ d.frame x hFrame
    (principal d.γ d.g₂ x)
    (fun a => actualFirstAdjointErrorFamily d (axis a) P.adjoint (P.center a) x) b
  have hCoarse : principalFirstErrorCoordinateCoarseL d P.adjoint P.center b x =
      d.radius x • (∑ j : I,d.frame x j b • (∑ i : I,
        (frameTensorMatrix d.γ d.frame x (principal d.γ d.g₂ x) i j+
          frameTensorMatrix d.γ d.frame x (principal d.γ d.g₂ x) j i) •
            actualFrameFirstAdjointErrorFamily d P.adjoint P.center i x)) := by
    unfold actualFrameFirstAdjointErrorFamily
    rw [hTensor]
    simp only [principalFirstErrorCoordinateCoarseL,principalFirstErrorCoordinateWeight,
      Finset.smul_sum,smul_smul]
  apply ContinuousLinearMap.ext
  intro u
  have hLow (i : I) := DFunLike.congr_fun (P.first.low_coarse i x hx) u
  simp only [ContinuousLinearMap.comp_apply] at hLow
  rw [hCoarse]
  simp only [ContinuousLinearMap.comp_apply,ActualFrameErrorEndpointPair.principalFirstErrorCoordinateHalfL,
    _root_.smul_apply,_root_.sum_apply,map_smul,map_sum,hLow]

end ShrinkingSpheres
