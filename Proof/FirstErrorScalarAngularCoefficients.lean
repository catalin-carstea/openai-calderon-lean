import Proof.ClosedCoordinateAngularCoefficient
import Proof.FirstErrorScalarCoefficients
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2800000
set_option maxSynthPendingDepth 30
set_option maxRecDepth 2300
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter
open scoped ContDiff Topology InnerProductSpace
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.DirichletFamily OAI.AnisotropicCalderon.SphereHarmonic

def coordinateScalarAngularTemplate (Q0 : SmoothCoefficientJets 2) (k i j : I) : ClosedCoefficientJets 3 :=
  (if k=j then smoothCoefficientClosureInclusionL 3 (coordinateScalarSmoothJet Q0 i) else 0)-
    (if k=i then smoothCoefficientClosureInclusionL 3 (coordinateScalarSmoothJet Q0 j) else 0)

lemma coordinateScalarAngularTemplate_half (Q0 : SmoothCoefficientJets 2)
    (hQ0 : ∀ z ∈ Metric.closedBall (0:X) 1,coefficientValue 2 Q0 =ᶠ[𝓝 z] (fun _ => (1:ℝ)))
    (k i j : I) :
    closedThreeJetHalfBoundaryScalarMultiplierL (coordinateScalarAngularTemplate Q0 k i j)=
      closedCoefficientAngularHalfL i j (smoothCoefficientClosureInclusionL 3 (coordinateScalarSmoothJet Q0 k)) := by
  rw [coordinateScalarClosedJet_angular_half Q0 hQ0]
  unfold coordinateScalarAngularTemplate
  rw [ContinuousLinearMap.map_sub]
  split_ifs <;> simp only [coordinateScalarClosedJet_half Q0 hQ0,ContinuousLinearMap.map_zero]

/-- Actual spatial angular coefficients of the scalar first-error normal
    form, with no added regularity on the completed coefficient input. -/
def firstErrorScalarAngularCoefficients (Q0 : SmoothCoefficientJets 2) (α : ℝ) (v : I → ℝ)
    (Q R : I → ClosedCoefficientJets 3) (i j : I) : TaylorGeneratorIndex → ClosedCoefficientJets 3
  | .taylor => α • (∑ k : I,v k • coordinateScalarAngularTemplate Q0 k i j)+
      α • (∑ k : I,closedCoordinateAngularCoefficient Q0 k i j (Q k) (R k))
  | .degree => α • (∑ k : I,closedCoordinateAngularCoefficient Q0 k i j (Q k) (R k))
  | .rotation k l => (-α) • closedCoordinateAngularCoefficient Q0 k i j (Q l) (R l)

lemma firstErrorScalarAngularCoefficients_half (Q0 : SmoothCoefficientJets 2)
    (hQ0 : ∀ z ∈ Metric.closedBall (0:X) 1,coefficientValue 2 Q0 =ᶠ[𝓝 z] (fun _ => (1:ℝ)))
    (α b : ℝ) (v : I → ℝ) (Q R : I → ClosedCoefficientJets 3) (i j : I)
    (hR : ∀ k,closedThreeJetHalfBoundaryScalarMultiplierL (R k)=closedCoefficientAngularHalfL i j (Q k))
    (a : TaylorGeneratorIndex) :
    closedThreeJetHalfBoundaryScalarMultiplierL (firstErrorScalarAngularCoefficients Q0 α v Q R i j a)=
      closedCoefficientAngularHalfL i j (firstErrorScalarCoefficients Q0 α b v Q a) := by
  cases a <;> simp only [firstErrorScalarAngularCoefficients,firstErrorScalarCoefficients,
    map_add,map_smul,map_sum,coordinateScalarAngularTemplate_half Q0 hQ0,
    closedCoordinateAngularCoefficient_half Q0 hQ0 _ _ _ _ _ (hR _),
    closedUnitCoefficient_angular_half Q0 hQ0,smul_zero,add_zero]
end ShrinkingSpheres
