import Proof.FirstErrorAdjointCommonBudget
import Proof.ActualFirstErrorAngularCoefficients
import Proof.NativeFirstErrorRadialHigherBounds
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
open Set MeasureTheory
open scoped ENNReal
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.EnergyBridge OAI.AnisotropicCalderon.DirichletFamily

def firstErrorHigherCommonBudget (F0 : SmoothCoefficientMatrix 2)
    (ha0 : MemLp (fun z => TauCeti.PDE.energyIntegrand (coefficientMatrixField 2 F0 z) 0 0) ⊤
      ((volume:Measure X).restrict ballOpens))
    (Q0 : SmoothCoefficientJets 2) (CG CKN CKH BS CQ CI CW K M0 CC CR : ℝ) : ℝ :=
  let CP := firstErrorAdjointCommonBudget F0 ha0 Q0 CG CKN CQ CI CW K M0 CC
  let C1 := firstErrorScalarFixedBudget Q0*(27*|M0| *K+3*K+15*CC)
  let CA := firstErrorScalarAngularCommonBudget Q0 K M0 CC CR
  let G := (taylorGeneratorFixedBudget F0 ha0 CG+2)*‖closedThreeJetHigherScalarMultiplierL‖*C1
  let R := (‖closedThreeJetHigherScalarMultiplierL‖*CKH+BS)*CA+radialScalarHigherCommonBudget*CQ*C1
  let Z := radialScalarHigherCommonBudget*CQ*C1
  CP+1+|G|+|R|+|Z|

private lemma extend_three_nonnegative_budgets (P a b c : ℝ) (hP : 1 ≤ P) :
    1 ≤ P+1+|a|+|b|+|c| ∧ P ≤ P+1+|a|+|b|+|c| ∧
      a ≤ P+1+|a|+|b|+|c| ∧ b ≤ P+1+|a|+|b|+|c| ∧ c ≤ P+1+|a|+|b|+|c| := by
  have ha := abs_nonneg a
  have hb := abs_nonneg b
  have hc := abs_nonneg c
  exact ⟨by linarith,by linarith,by linarith [le_abs_self a],by linarith [le_abs_self b],by linarith [le_abs_self c]⟩

lemma firstErrorHigherCommonBudget_bounds (F0 : SmoothCoefficientMatrix 2)
    (ha0 : MemLp (fun z => TauCeti.PDE.energyIntegrand (coefficientMatrixField 2 F0 z) 0 0) ⊤
      ((volume:Measure X).restrict ballOpens))
    (Q0 : SmoothCoefficientJets 2) (CG CKN CKH BS CQ CI CW K M0 CC CR : ℝ) :
    let CP := firstErrorAdjointCommonBudget F0 ha0 Q0 CG CKN CQ CI CW K M0 CC
    let C1 := firstErrorScalarFixedBudget Q0*(27*|M0| *K+3*K+15*CC)
    let CA := firstErrorScalarAngularCommonBudget Q0 K M0 CC CR
    let B := firstErrorHigherCommonBudget F0 ha0 Q0 CG CKN CKH BS CQ CI CW K M0 CC CR
    1 ≤ B ∧ CP ≤ B ∧
      (taylorGeneratorFixedBudget F0 ha0 CG+2)*‖closedThreeJetHigherScalarMultiplierL‖*C1 ≤ B ∧
      (‖closedThreeJetHigherScalarMultiplierL‖*CKH+BS)*CA+radialScalarHigherCommonBudget*CQ*C1 ≤ B ∧
      radialScalarHigherCommonBudget*CQ*C1 ≤ B := by
  exact extend_three_nonnegative_budgets _ _ _ _
    (firstErrorAdjointCommonBudget_bounds F0 ha0 Q0 CG CKN CQ CI CW K M0 CC).1
end ShrinkingSpheres
