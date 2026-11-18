import Mathlib.Analysis.Analytic.Constructions
import Mathlib.Analysis.Analytic.IteratedFDeriv
import Mathlib.Analysis.Normed.Operator.Banach

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxSynthPendingDepth 30
open Set Filter
open scoped ContDiff Topology
namespace ShrinkingSpheres

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

def operatorResolvent (A : E →L[ℝ] E) : E →L[ℝ] E := Ring.inverse (1-A)

lemma contDiffAt_operatorResolvent_zero :
    ContDiffAt ℝ ∞ (operatorResolvent (E:=E)) 0 :=
  (analyticAt_inverse_one_sub ℝ (E →L[ℝ] E)).contDiffAt

/-- Explicit all-order Banach resolvent jets from the geometric series.
    Each derivative is a sum over n! permutations, each of norm at most
    the product of the input norms. No operator-space compactness is used. -/
theorem norm_iteratedFDeriv_operatorResolvent_zero (n : ℕ) :
    ‖iteratedFDeriv ℝ n (operatorResolvent (E:=E)) 0‖ ≤ (n.factorial:ℝ) := by
  have hOne : ‖(1:E →L[ℝ] E)‖ ≤ 1 := ContinuousLinearMap.norm_id_le
  have hCoeff : ‖formalMultilinearSeries_geometric ℝ (E →L[ℝ] E) n‖ ≤ 1 :=
    (formalMultilinearSeries_geometric_apply_norm_le ℝ (E →L[ℝ] E) n).trans (max_le le_rfl hOne)
  have hSeries := hasFPowerSeriesOnBall_inverse_one_sub ℝ (E →L[ℝ] E)
  apply ContinuousMultilinearMap.opNorm_le_bound (Nat.cast_nonneg _)
  intro v
  change ‖iteratedFDeriv ℝ n (fun A : E →L[ℝ] E => Ring.inverse (1-A)) 0 v‖ ≤ _
  rw [hSeries.iteratedFDeriv_eq_sum_of_completeSpace v]
  have hTerm (σ : Equiv.Perm (Fin n)) :
      ‖formalMultilinearSeries_geometric ℝ (E →L[ℝ] E) n (fun i => v (σ i))‖ ≤ ∏ i,‖v i‖ := by
    have hh := (formalMultilinearSeries_geometric ℝ (E →L[ℝ] E) n).le_opNorm (fun i => v (σ i))
    have hProd : (∏ i,‖v (σ i)‖) = ∏ i,‖v i‖ := Fintype.prod_equiv σ _ _ (fun _ => rfl)
    exact hh.trans ((mul_le_mul_of_nonneg_right hCoeff (Finset.prod_nonneg (fun _ _ => norm_nonneg _))).trans_eq
      (by rw [one_mul,hProd]))
  exact (norm_sum_le _ _).trans ((Finset.sum_le_sum (fun σ _ => hTerm σ)).trans_eq
    (by simp only [Finset.sum_const,Finset.card_univ,Fintype.card_perm,Fintype.card_fin,nsmul_eq_mul]))

lemma operatorResolvent_finite_jet_bound (N : ℕ) (n : ℕ) (hn : n ≤ N) :
    ‖iteratedFDeriv ℝ n (operatorResolvent (E:=E)) 0‖ ≤ (N.factorial:ℝ) :=
  (norm_iteratedFDeriv_operatorResolvent_zero n).trans (by exact_mod_cast Nat.factorial_le hn)

end ShrinkingSpheres
