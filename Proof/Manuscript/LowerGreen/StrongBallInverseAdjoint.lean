module

public import Proof.Manuscript.LowerGreen.StrongBallSmoothInverse

import Proof.ReleasedAnalysis.TauCeti.Analysis.PDE.SymmetricEnergy
import Mathlib.Tactic

public section

noncomputable section

open Set Filter MeasureTheory
open CalderonN CalderonN.BallDirichlet TauCeti
open scoped ENNReal InnerProductSpace Matrix.Norms.Elementwise

namespace CalderonPaper.LowerGreen

variable {n : ℕ} [NeZero n]

set_option maxHeartbeats 2200000 in
/-- On ambient volume L² the Dirichlet inverse is symmetric for a
symmetric divergence coefficient. -/
theorem fullStrongBallInverseL_zero_inner
    (A : SmoothCoefficientMatrix n 2) {lo hi : ℝ}
    (hEll : PDE.UniformlyEllipticOn (fixedBallOpens n : Set (X n)) (coefficientMatrixField 2 A) lo hi)
    (hSym : ∀ x ∈ (fixedBallOpens n : Set (X n)), (coefficientMatrixField 2 A x).IsSymm)
    (f g : BallSobolev n 0) :
    ⟪Wkp.value 2 (fullStrongBallInverseL 0 A f),g⟫_ℝ =
      ⟪f,Wkp.value 2 (fullStrongBallInverseL 0 A g)⟫_ℝ := by
  let O := fixedBallOpens n
  let L := strongDirichletOperator fixedSobolevCalculus 0 A
  let D := strongDirichletProjectionL n 0
  let U := L.inverse f
  let V := L.inverse g
  have hInv := strongDirichletOperator_isInvertible_of_elliptic
    fixedSobolevCalculus fixedDirichletRegularity 0 A hEll
  have hEnergy (u v : FixedBallH1Zero n) :
      PDE.energyFormH1 (coefficientMatrixField 2 A) 0 0 (u : FixedBallH1 n) (v : FixedBallH1 n) =
      PDE.energyFormH1 (coefficientMatrixField 2 A) 0 0 (v : FixedBallH1 n) (u : FixedBallH1 n) := by
    simp only [PDE.energyFormH1_def]
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem O.isOpen.measurableSet] with x hx
    exact PDE.energyIntegrand_zero_drift_comm_of_isSymm (hSym x hx) 0 _ _
  have hU := strongCoefficientOperator_energy fixedSobolevCalculus 0 A U (D V)
  have hV := strongCoefficientOperator_energy fixedSobolevCalculus 0 A V (D U)
  rw [show L U = f from hInv.self_apply_inverse f, Wkp.value_zero, PDE.dirichletForcing_apply] at hU
  rw [show L V = g from hInv.self_apply_inverse g, Wkp.value_zero, PDE.dirichletForcing_apply] at hV
  have hVal (w : StrongDirichletSpace n 0) :
      W1p.value (D w : FixedBallH1 n) = Wkp.value 2 w.1 := by
    rw [strongDirichletProjectionL_apply,Wkp.value_firstOrder]
  rw [hVal] at hU hV
  simp only [fullStrongBallInverseL,ContinuousLinearMap.comp_apply,Submodule.subtypeL_apply]
  change ⟪Wkp.value 2 U.1,g⟫_ℝ = ⟪f,Wkp.value 2 V.1⟫_ℝ
  exact (real_inner_comm _ _).trans (hV.trans ((hEnergy _ _).trans hU.symm))

end CalderonPaper.LowerGreen

end
