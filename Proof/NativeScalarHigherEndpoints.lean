import Proof.ScalarRotationDataHigherEndpoints
import Proof.NativeScalarRotationGraph
import Proof.NativeScalarOperatorFamily
import Proof.ClosedFourJetAngularDerivative
import Proof.ZeroOrderRotationHighLift
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3200000
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

def scalarRotationWitnessFamily (A : NativeAdjointHalfScalarNeighborhoodData s h hK CK CJ)
    (Q0 : SmoothCoefficientJets 2) (Q : NormalFrameRelativeParameter → ClosedCoefficientJets 4)
    (i j : I) (p : NormalFrameRelativeParameter) :
    SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ) :=
  A.scalarRotationWitnessFromData (fun x => closedCoefficientLowerJetsL 3 (Q x))
    (fun ij x => closedFourJetAngularDerivativeL Q0 ij.1 ij.2 (Q x)) i j p

def scalarHigherFamily (A : NativeAdjointHalfScalarNeighborhoodData s h hK CK CJ)
    (Q0 : SmoothCoefficientJets 2) (Q : NormalFrameRelativeParameter → ClosedCoefficientJets 4)
    (p : NormalFrameRelativeParameter) :
    SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (3/2:ℝ) :=
  A.scalarHigherFamilyFromRotationData (fun x => closedCoefficientLowerJetsL 3 (Q x))
    (fun ij x => closedFourJetAngularDerivativeL Q0 ij.1 ij.2 (Q x)) p

/-- The constructed higher scalar commutator agrees through the physical
inclusion with the SAME actual half scalar commutator. -/
lemma scalarHigherFamily_compatible
    (A : NativeAdjointHalfScalarNeighborhoodData s h hK CK CJ) (hΩ : IsOpen Ω)
    (hF0 : ∀ z ∈ Metric.closedBall (0:X) 2,coefficientMatrixField 2 F0 z=1)
    (he : ∀ i j,metricPair d.γ y ((frameVectorLinear d.frame y) (axis i))
      ((frameVectorLinear d.frame y) (axis j))=if i=j then 1 else 0)
    (Q0 : SmoothCoefficientJets 2)
    (hQ0 : ∀ z ∈ Metric.closedBall (0:X) 1,coefficientValue 2 Q0 =ᶠ[nhds z] (fun _ => (1:ℝ)))
    (Q : NormalFrameRelativeParameter → ClosedCoefficientJets 4) :
    let p : NormalFrameRelativeParameter := ((y,frameVectorLinear d.frame y),0)
    (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)).comp (A.scalarHigherFamily Q0 Q p)=
      (s.response.adjointHalfScalarCommutator F0 A.kernel (closedCoefficientLowerJetsL 3 (Q p)) p).comp
        (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)) := by
  exact A.scalarHigherFamilyFromRotationData_compatible hΩ hF0 he _ _
    (fun i j => closedFourJetAngularDerivative_half Q0 hQ0 i j _)
end NativeAdjointHalfScalarNeighborhoodData
end ShrinkingSpheres
