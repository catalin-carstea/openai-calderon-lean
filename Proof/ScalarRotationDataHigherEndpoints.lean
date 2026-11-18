import Proof.NativeScalarRotationGraph
import Proof.NativeScalarOperatorFamily
import Proof.ZeroOrderRotationHighLift
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxSynthPendingDepth 30
set_option maxRecDepth 2500
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
open Set
open scoped ContDiff Topology InnerProductSpace
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.DirichletFamily OAI.AnisotropicCalderon.SphereHarmonic
namespace NativeAdjointHalfScalarNeighborhoodData
variable {Y Ω : Set X} {d : Data} {y : X} {F0 : SmoothCoefficientMatrix 2}
  {CQ CI CW CF CA CM : ℝ}
  {s : NativeRelativeHorizontalTaylorData Y Ω d y F0 CQ CI CW CF CA CM}
  {K CK CJ : ℝ} {h : Elliptic Ω K d.γ} {hK : 0 < K}

def scalarRotationWitnessFromData (A : NativeAdjointHalfScalarNeighborhoodData s h hK CK CJ)
    (Q : NormalFrameRelativeParameter → ClosedCoefficientJets 3)
    (R : I × I → NormalFrameRelativeParameter → ClosedCoefficientJets 3)
    (i j : I) (p : NormalFrameRelativeParameter) :
    SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ) :=
  normalFrameRelativeAngularDerivative d.γ A.scalarOperatorFamily i j p (Q p)+
    A.scalarOperatorFamily p (R (i,j) p)

def scalarHigherFamilyFromRotationData (A : NativeAdjointHalfScalarNeighborhoodData s h hK CK CJ)
    (Q : NormalFrameRelativeParameter → ClosedCoefficientJets 3)
    (R : I × I → NormalFrameRelativeParameter → ClosedCoefficientJets 3)
    (p : NormalFrameRelativeParameter) :
    SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (3/2:ℝ) :=
  zeroOrderRotationHighLiftL (A.scalarOperatorFamily p (Q p))
    (fun i j => A.scalarRotationWitnessFromData Q R i j p)

lemma scalarHigherFamilyFromRotationData_compatible
    (A : NativeAdjointHalfScalarNeighborhoodData s h hK CK CJ) (hΩ : IsOpen Ω)
    (hF0 : ∀ z ∈ Metric.closedBall (0:X) 2,coefficientMatrixField 2 F0 z=1)
    (he : ∀ i j,metricPair d.γ y ((frameVectorLinear d.frame y) (axis i))
      ((frameVectorLinear d.frame y) (axis j))=if i=j then 1 else 0)
    (Q : NormalFrameRelativeParameter → ClosedCoefficientJets 3)
    (R : I × I → NormalFrameRelativeParameter → ClosedCoefficientJets 3)
    (hR : ∀ i j,closedThreeJetHalfBoundaryScalarMultiplierL (R (i,j) ((y,frameVectorLinear d.frame y),0))=
      closedCoefficientAngularHalfL i j (Q ((y,frameVectorLinear d.frame y),0))) :
    let p : NormalFrameRelativeParameter := ((y,frameVectorLinear d.frame y),0)
    (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)).comp
      (A.scalarHigherFamilyFromRotationData Q R p)=
      (s.response.adjointHalfScalarCommutator F0 A.kernel (Q p) p).comp
        (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)) := by
  let p : NormalFrameRelativeParameter := ((y,frameVectorLinear d.frame y),0)
  change (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)).comp
    (zeroOrderRotationHighLiftL (A.scalarOperatorFamily p (Q p))
      (fun i j => A.scalarRotationWitnessFromData Q R i j p))=_
  rw [← scalarOperatorFamily_apply A p (Q p)]
  apply zeroOrderRotationHighLiftL_compatible
  intro u i j
  have hh := A.scalar_rotation_graph_of_angular_coefficient hΩ hF0 he (Q p) (R (i,j) p) i j (hR i j) u
  simpa only [scalarRotationWitnessFromData,p,scalarOperatorFamily_angular_apply A he,
    scalarOperatorFamily_apply] using hh
end NativeAdjointHalfScalarNeighborhoodData
end ShrinkingSpheres
