import Proof.NativeFirstErrorAdjointRemainderNorm
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
open Set Filter MeasureTheory
open scoped ContDiff Topology InnerProductSpace ENNReal
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.EnergyBridge OAI.AnisotropicCalderon.DirichletFamily
open OAI.AnisotropicCalderon.SphereHarmonic

def firstErrorAdjointCommonBudget (F0 : SmoothCoefficientMatrix 2)
    (ha0 : MemLp (fun z => TauCeti.PDE.energyIntegrand (coefficientMatrixField 2 F0 z) 0 0) ⊤
      ((volume:Measure X).restrict ballOpens))
    (Q0 : SmoothCoefficientJets 2) (CG CK CQ CI CW K M0 CC : ℝ) : ℝ :=
  let CB := taylorGeneratorFixedBudget F0 ha0 CG
  let C1 := firstErrorScalarFixedBudget Q0*(27*|M0| *K+3*K+15*CC)
  let CZ := radialScalarEndpointBudget CQ
  1+|CB*‖closedThreeJetHalfBoundaryScalarMultiplierL‖*C1|+
    |(‖closedThreeJetHalfBoundaryScalarMultiplierL‖*CK+CB+CZ)*C1|+
    |(‖closedThreeJetNegativeScalarMultiplierL‖*CK+nativeNegativeScalarFixedBudget F0 ha0 CQ CI CW+CZ)*C1|+
    |CZ*C1|

private lemma abs_four_budget (a b c d : ℝ) :
    1 ≤ 1+|a|+|b|+|c|+|d| ∧ a ≤ 1+|a|+|b|+|c|+|d| ∧
      b ≤ 1+|a|+|b|+|c|+|d| ∧ c ≤ 1+|a|+|b|+|c|+|d| ∧ d ≤ 1+|a|+|b|+|c|+|d| := by
  have ha := abs_nonneg a
  have hb := abs_nonneg b
  have hc := abs_nonneg c
  have hd := abs_nonneg d
  refine ⟨by linarith,by linarith [le_abs_self a],by linarith [le_abs_self b],
    by linarith [le_abs_self c],by linarith [le_abs_self d]⟩

lemma firstErrorAdjointCommonBudget_bounds (F0 : SmoothCoefficientMatrix 2)
    (ha0 : MemLp (fun z => TauCeti.PDE.energyIntegrand (coefficientMatrixField 2 F0 z) 0 0) ⊤
      ((volume:Measure X).restrict ballOpens))
    (Q0 : SmoothCoefficientJets 2) (CG CK CQ CI CW K M0 CC : ℝ) :
    let CB := taylorGeneratorFixedBudget F0 ha0 CG
    let C1 := firstErrorScalarFixedBudget Q0*(27*|M0| *K+3*K+15*CC)
    let CZ := radialScalarEndpointBudget CQ
    let CP := firstErrorAdjointCommonBudget F0 ha0 Q0 CG CK CQ CI CW K M0 CC
    1 ≤ CP ∧ CB*‖closedThreeJetHalfBoundaryScalarMultiplierL‖*C1 ≤ CP ∧
      (‖closedThreeJetHalfBoundaryScalarMultiplierL‖*CK+CB+CZ)*C1 ≤ CP ∧
      (‖closedThreeJetNegativeScalarMultiplierL‖*CK+nativeNegativeScalarFixedBudget F0 ha0 CQ CI CW+CZ)*C1 ≤ CP ∧
      CZ*C1 ≤ CP := abs_four_budget _ _ _ _
end ShrinkingSpheres
