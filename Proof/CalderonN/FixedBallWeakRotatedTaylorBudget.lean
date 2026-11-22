module

public import Proof.CalderonN.FixedBallWeakRotatedTaylor
public import Proof.CalderonN.WeakConormalRotatedTaylorJets

import Mathlib.Tactic

/-! Quadratic joint Taylor bounds for the weak form of the genuine
conormal rotation commutator. -/

public section

noncomputable section
open Set Filter Metric
open scoped ContDiff Topology Matrix.Norms.Elementwise
set_option autoImplicit false
set_option maxHeartbeats 9000000
set_option maxSynthPendingDepth 29
set_option backward.isDefEq.respectTransparency false
namespace CalderonN

open BallDirichlet TauCeti PDE
attribute [local instance] W1p0.instNormedAddCommGroup W1p0.instInnerProductSpace
variable {dim : ℕ} [NeZero dim] [Nontrivial (Fin dim)]

theorem exists_fixedBall_rotatedWeakConormal_family_jet_budget
    (N : ℕ) (B : ℝ) (hB : 0 ≤ B) :
    ∃ δ C : ℝ, 0 < δ ∧ 0 ≤ C ∧ ∀ r ∈ Icc (0:ℝ) δ, ∀ x : X dim × ℝ,
      ∀ E₁ E₂ T₁ T₂ : X dim × ℝ → FixedBallEnergyOperator dim,
      LocalSmoothJetBudget E₁ x N B → LocalSmoothJetBudget E₂ x N B →
      LocalSmoothJetBudget T₁ x N B → LocalSmoothJetBudget T₂ x N B →
      LocalSmoothJetBudget (fun p => fixedBallWeakConormalRotatedTaylor r
        (E₁ p) (E₂ p) (T₁ p) (T₂ p)) x N (C*r^2) := by
  obtain ⟨δ,C,hδ,hC,h⟩ := exists_weakConormal_rotatedTaylor_jet_budget (P:=X dim × ℝ)
    (H:=FixedBallH1 dim) (F:=SphereSobolev dim (1/2:ℝ)) (Z:=FixedBallH1Zero dim)
    (fixedBallZeroInclusionL dim) (fixedBallFlatEnergyL dim) (harmonicFirstOrderLift dim)
    (fixedBallFlatWeakEnergy_isInvertible dim) fixedBallFlatEnergyL_harmonicFirstOrderLift_zero N B hB
  refine ⟨δ,C,hδ,hC,?_⟩
  intro r hr x E₁ E₂ T₁ T₂ hE₁ hE₂ hT₁ hT₂
  have hR := h r hr x E₁ E₂ T₁ T₂ hE₁ hE₂ hT₁ hT₂
  let P₀ := harmonicFirstOrderLift dim
  let U (p : X dim × ℝ) := weakEnergyPoissonOperatorL (fixedBallZeroInclusionL dim)
    (fixedBallFlatEnergyL dim+r • E₁ p+r^2 • E₂ p) P₀
  let C₀ (p : X dim × ℝ) := (r • T₁ p+r^2 • T₂ p).bilinearComp (U p) (U p)-
      r • (T₁ p).bilinearComp P₀ P₀
  have hEq : (fun p => fixedBallWeakConormalRotatedTaylor r (E₁ p) (E₂ p) (T₁ p) (T₂ p)) = C₀ := by
    funext p
    ext f g : 2
    simp only [fixedBallWeakConormalRotatedTaylor,fixedBallWeakRotatedSubtract,
      fixedBallWeakRotatedCompose,fixedBallWeakRotatedSolution,C₀,U,P₀,
      ContinuousLinearMap.bilinearComp_apply,sub_apply,smul_apply]
  rw [hEq]
  exact hR

end CalderonN
