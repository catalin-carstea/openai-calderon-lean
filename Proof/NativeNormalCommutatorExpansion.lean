import Proof.NativeScalarCommutatorRest
import Proof.ScalarNormalExpansionAlgebra
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter MeasureTheory
open scoped ContDiff Topology ENNReal
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.EnergyBridge OAI.AnisotropicCalderon.DirichletFamily
open OAI.AnisotropicCalderon.SphereHarmonic
namespace NativeRelativeHorizontalTaylorData
variable {Y Ω : Set X} {d : Data} {y : X} {F0 : SmoothCoefficientMatrix 2} {CQ CI CW CF CA CM C : ℝ}
lemma fullAdjoint_normal_scalar_commutator_expansion
    (s : NativeRelativeHorizontalTaylorData Y Ω d y F0 CQ CI CW CF CA CM)
    (ha0 : MemLp (fun z => TauCeti.PDE.energyIntegrand (coefficientMatrixField 2 F0 z) 0 0) ⊤
      ((volume:Measure X).restrict ballOpens))
    (hF0 : ∀ z ∈ Metric.closedBall (0:X) 2,coefficientMatrixField 2 F0 z=1)
    (R : RelativeNormalScalarRemainderFamily d y C) (Q : SmoothCoefficientJets 2)
    (hQ : ∀ z ∈ Metric.closedBall (0:X) 1,coefficientValue 2 Q =ᶠ[𝓝 z] (fun _ => (1:ℝ)))
    (p : NormalFrameRelativeParameter) :
    s.response.fullAdjointScalarCommutator F0 ha0 (R.normalCoefficient Q p) p=
      d.radius y • closedNegativeDegreeScalarCommutatorL F0 ha0
        (linearScalarClosedCoefficientL Q (normalFrameRelativeFirstCovector d.γ d.g₁ p))+
      s.scalarCommutatorRest ha0 (R.normalCoefficient Q) R.closed p := by
  have hOne := smooth_unit_closed_scalar_one (coefficientThirdJet Q) (fun w => by
    rw [coefficientValue_coefficientThirdJet]
    exact (hQ w.val (Metric.sphere_subset_closedBall w.property)).eq_of_nhds)
  have hUnit := closedNegativeDegreeScalarCommutator_unit F0 ha0
    (fun z hz => hF0 z (unitBall_subset_closedBall_two hz)) s.point.flatStrong _ hOne
  have hDegree : closedNegativeDegreeScalarCommutatorL F0 ha0 (R.normalCoefficient Q p)=
      d.radius y • closedNegativeDegreeScalarCommutatorL F0 ha0
        (linearScalarClosedCoefficientL Q (normalFrameRelativeFirstCovector d.γ d.g₁ p))+
        closedNegativeDegreeScalarCommutatorL F0 ha0 (R.closed p) := by
    simp only [RelativeNormalScalarRemainderFamily.normalCoefficient,map_add,map_smul,hUnit,zero_add]
  exact scalar_expansion_algebra _ _ _ _ _ _ _ hDegree
end NativeRelativeHorizontalTaylorData
end ShrinkingSpheres
