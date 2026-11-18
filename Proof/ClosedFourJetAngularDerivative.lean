import Proof.ClosedCoefficientDerivativeLowerJets
import Proof.ClosedCoordinateCoefficientProduct
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
open Set
open scoped ContDiff Topology
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.DirichletFamily OAI.AnisotropicCalderon.SphereHarmonic
open OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

def closedFourJetAngularDerivativeL (Q0 : SmoothCoefficientJets 2) (i j : I) :
    ClosedCoefficientJets 4 →L[ℝ] ClosedCoefficientJets 3 :=
  (closedCoordinateCoefficientProductL Q0 i).comp (closedCoefficientDirectionalDerivativeL 3 (axis j))-
    (closedCoordinateCoefficientProductL Q0 j).comp (closedCoefficientDirectionalDerivativeL 3 (axis i))

/-- The completed angular coefficient has the actual half-boundary multiplier
of the scalar rotation product rule; the extra input jet is explicit. -/
lemma closedFourJetAngularDerivative_half (Q0 : SmoothCoefficientJets 2)
    (hQ0 : ∀ z ∈ Metric.closedBall (0:X) 1,coefficientValue 2 Q0 =ᶠ[nhds z] (fun _ => (1:ℝ)))
    (i j : I) (Q : ClosedCoefficientJets 4) :
    closedThreeJetHalfBoundaryScalarMultiplierL (closedFourJetAngularDerivativeL Q0 i j Q)=
      closedCoefficientAngularHalfL i j (closedCoefficientLowerJetsL 3 Q) := by
  have hD (v : X) :
      closedThreeJetHalfBoundaryScalarMultiplierL (closedCoefficientDirectionalDerivativeL 3 v Q)=
        closedTwoJetHalfBoundaryScalarMultiplierL
          (closedCoefficientDirectionalDerivativeL 2 v (closedCoefficientLowerJetsL 3 Q)) := by
    change closedTwoJetHalfBoundaryScalarMultiplierL
      (closedCoefficientLowerJetsL 2 (closedCoefficientDirectionalDerivativeL 3 v Q))=_
    rw [closedCoefficientDirectionalDerivative_lowerJets 2 v Q]
  change closedThreeJetHalfBoundaryScalarMultiplierL
    (closedCoordinateCoefficientProductL Q0 i (closedCoefficientDirectionalDerivativeL 3 (axis j) Q)-
      closedCoordinateCoefficientProductL Q0 j (closedCoefficientDirectionalDerivativeL 3 (axis i) Q))=_
  rw [ContinuousLinearMap.map_sub closedThreeJetHalfBoundaryScalarMultiplierL]
  rw [closedCoordinateCoefficientProduct_half Q0 hQ0 i,closedCoordinateCoefficientProduct_half Q0 hQ0 j]
  simp only [hD,closedCoefficientAngularHalfL,_root_.sub_apply,ContinuousLinearMap.comp_apply,ContinuousLinearMap.compL_apply]
end ShrinkingSpheres
