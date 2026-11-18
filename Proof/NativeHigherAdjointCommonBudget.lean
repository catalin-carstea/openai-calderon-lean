import Proof.NativeScalarBoundedHigherCommutator
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxSynthPendingDepth 30
set_option maxRecDepth 2600
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set MeasureTheory
open scoped ContDiff Topology ENNReal
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.EnergyBridge OAI.AnisotropicCalderon.DirichletFamily
open OAI.AnisotropicCalderon.SphereHarmonic

/-- A common numeric budget for the six SAME-packet higher commutator
factors, independent of the two scales appearing at the point of use. -/
def nativeHigherAdjointCommonBudget (F0 : SmoothCoefficientMatrix 2)
    (ha0 : MemLp (fun z => TauCeti.PDE.energyIntegrand (coefficientMatrixField 2 F0 z) 0 0) ⊤
      ((volume:Measure X).restrict ballOpens)) (CG CKN BKH BS CQB CZB CAug : ℝ) : ℝ :=
  let CB := taylorGeneratorFixedBudget F0 ha0 CG
  1+|((CB+2)*‖closedThreeJetHigherScalarMultiplierL‖)*CQB|+
    |(‖closedThreeJetHigherScalarMultiplierL‖*BKH+BS)*CAug+CZB|+
    |(‖closedThreeJetHalfBoundaryScalarMultiplierL‖*CKN+CB)*CQB+CZB|+|CZB|

lemma nativeHigherAdjointCommonBudget_bounds (F0 : SmoothCoefficientMatrix 2)
    (ha0 : MemLp (fun z => TauCeti.PDE.energyIntegrand (coefficientMatrixField 2 F0 z) 0 0) ⊤
      ((volume:Measure X).restrict ballOpens)) (CG CKN BKH BS CQB CZB CAug : ℝ) :
    let CB := taylorGeneratorFixedBudget F0 ha0 CG
    let C := nativeHigherAdjointCommonBudget F0 ha0 CG CKN BKH BS CQB CZB CAug
    1 ≤ C ∧ ((CB+2)*‖closedThreeJetHigherScalarMultiplierL‖)*CQB ≤ C ∧
      (‖closedThreeJetHigherScalarMultiplierL‖*BKH+BS)*CAug+CZB ≤ C ∧
      (‖closedThreeJetHalfBoundaryScalarMultiplierL‖*CKN+CB)*CQB+CZB ≤ C ∧ CZB ≤ C := by
  dsimp only [nativeHigherAdjointCommonBudget]
  refine ⟨?_,?_,?_,?_,?_⟩ <;> linarith only [
    le_abs_self (((taylorGeneratorFixedBudget F0 ha0 CG+2)*‖closedThreeJetHigherScalarMultiplierL‖)*CQB),
    le_abs_self ((‖closedThreeJetHigherScalarMultiplierL‖*BKH+BS)*CAug+CZB),
    le_abs_self ((‖closedThreeJetHalfBoundaryScalarMultiplierL‖*CKN+taylorGeneratorFixedBudget F0 ha0 CG)*CQB+CZB),
    le_abs_self CZB,
    abs_nonneg (((taylorGeneratorFixedBudget F0 ha0 CG+2)*‖closedThreeJetHigherScalarMultiplierL‖)*CQB),
    abs_nonneg ((‖closedThreeJetHigherScalarMultiplierL‖*BKH+BS)*CAug+CZB),
    abs_nonneg ((‖closedThreeJetHalfBoundaryScalarMultiplierL‖*CKN+taylorGeneratorFixedBudget F0 ha0 CG)*CQB+CZB),abs_nonneg CZB]
end ShrinkingSpheres
