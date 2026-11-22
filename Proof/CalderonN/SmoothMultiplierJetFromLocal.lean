module

public import Proof.CalderonN.NormalizedMultiplierCommutator
public import Proof.CalderonN.ParametricSphereMultiplierJets

import Proof.CalderonN.ChristoffelDerivative
import Proof.CalderonN.BallRotationCalculus
import Mathlib.Tactic

/-! The two derivatives used by the bulk multiplication forcing and
the radial product term follow from the same local scalar jet budget. -/

public section

noncomputable section
open Set Metric
open scoped ContDiff
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace CalderonN

open BallDirichlet
variable {dim : ℕ} [NeZero dim] [Nontrivial (Fin dim)]

theorem smoothMultiplierJetBound_of_local (m : SmoothData dim) (C : ℝ) (hC : 0 ≤ C)
    (h : ∀ z ∈ closedBall (0:X dim) 1,LocalSmoothJetBudget m.1 z 2 C) :
    SmoothMultiplierJetBound m (2*C) := by
  intro z hz
  have hz₁ := (mem_ball_zero_iff.mp hz).le
  have hJet := h z (ball_subset_closedBall hz)
  have h₁ : ‖fderiv ℝ m.1 z‖ ≤ C := hJet.fderiv.value_norm_le
  have h₂ : ‖fderiv ℝ (fderiv ℝ m.1) z‖ ≤ C := hJet.fderiv.fderiv.value_norm_le
  have hCC : C ≤ 2*C := by linarith only [hC]
  refine ⟨⟨h₁.trans hCC,?_⟩,?_,?_⟩
  · intro i
    apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
    intro v
    rw [Real.norm_eq_abs]
    exact (fderiv_coordDeriv_abs_le m.1 z i
      ((m.2.fderiv_right (m:=∞) (by simp)).differentiable (by simp) z) C h₂ v).trans
      (mul_le_mul_of_nonneg_right hCC (norm_nonneg _))
  · exact ((fderiv ℝ m.1 z).le_opNorm z).trans
      ((mul_le_mul h₁ hz₁ (norm_nonneg _) hC).trans (by linarith only [hCC]))
  · apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
    intro v
    have hId := fderiv_linearDirectional_apply (ContinuousLinearMap.id ℝ (X dim)) m.2 z v
    change fderiv ℝ (fun x => fderiv ℝ m.1 x x) z v =
      fderiv ℝ (fderiv ℝ m.1) z v z+fderiv ℝ m.1 z v at hId
    rw [hId]
    have ha : ‖fderiv ℝ (fderiv ℝ m.1) z v z‖ ≤ C*‖v‖ := by
      refine ((fderiv ℝ (fderiv ℝ m.1) z v).le_opNorm z).trans ?_
      calc
        _ ≤ ‖fderiv ℝ (fderiv ℝ m.1) z v‖ := by
          simpa only [mul_one] using mul_le_mul_of_nonneg_left hz₁ (norm_nonneg _)
        _ ≤ C*‖v‖ := ((fderiv ℝ (fderiv ℝ m.1) z).le_opNorm v).trans
          (mul_le_mul_of_nonneg_right h₂ (norm_nonneg _))
    have hb : ‖fderiv ℝ m.1 z v‖ ≤ C*‖v‖ :=
      ((fderiv ℝ m.1 z).le_opNorm v).trans (mul_le_mul_of_nonneg_right h₁ (norm_nonneg _))
    exact ((norm_add_le _ _).trans (add_le_add ha hb)).trans_eq (by ring)

end CalderonN
