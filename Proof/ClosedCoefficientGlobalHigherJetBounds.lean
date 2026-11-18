import Proof.ClosedLocalCoefficientJets
import Proof.Archive.ClosedCoefficientJets
import Proof.FiniteJetBoundCalculus
import Proof.CommonSupportMultiplierDerivative

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option maxSynthPendingDepth 30
open Set Filter
open scoped ContDiff Topology BoundedContinuousFunction
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.EnergyBridge OAI.AnisotropicCalderon.DirichletFamily

variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]

lemma iteratedFDeriv_closedCoefficient_jet_eval (r : ℕ) (Q : P → ClosedCoefficientJets r)
    (p : P) (hQ : ContDiffAt ℝ ∞ Q p) (n : ℕ) (v : Fin n → P) (j : Fin (r+1)) (z : X) :
    (iteratedFDeriv ℝ n Q p v).val j z = iteratedFDeriv ℝ n (fun t => (Q t).val j z) p v := by
  let ev := closedCoefficientJetEvaluationL r j z
  have hh := ev.iteratedFDeriv_comp_left hQ (i:=n) (by simp)
  exact (congrArg (fun A => A v) hh).symm

/-- Uniform global spatial jet bounds control the completed coefficient
    jet in operator norm, including every parameter derivative. -/
theorem norm_iteratedFDeriv_closedCoefficient_of_global_jet_bounds_le
    (r : ℕ) (Q : P → ClosedCoefficientJets r) (p : P) (hQ : ContDiffAt ℝ ∞ Q p)
    (n : ℕ) (C : ℝ) (hC : 0 ≤ C)
    (hJets : ∀ j : Fin (r+1),∀ z : X,‖iteratedFDeriv ℝ n (fun t => (Q t).val j z) p‖ ≤ C) :
    ‖iteratedFDeriv ℝ n Q p‖ ≤ C := by
  apply ContinuousMultilinearMap.opNorm_le_bound hC
  intro v
  have hProd : 0 ≤ C*∏ i,‖v i‖ := mul_nonneg hC (Finset.prod_nonneg (fun _ _ => norm_nonneg _))
  change ‖(iteratedFDeriv ℝ n Q p v).val‖ ≤ C*∏ i,‖v i‖
  apply (pi_norm_le_iff_of_nonneg hProd).mpr
  intro j
  apply (BoundedContinuousFunction.norm_le hProd).mpr
  intro z
  rw [iteratedFDeriv_closedCoefficient_jet_eval r Q p hQ]
  exact ((iteratedFDeriv ℝ n (fun t => (Q t).val j z) p).le_opNorm v).trans
    (mul_le_mul_of_nonneg_right (hJets j z) (Finset.prod_nonneg (fun _ _ => norm_nonneg _)))

variable [FiniteDimensional ℝ P]

theorem norm_iteratedFDeriv_commonSupportClosedCoefficientFamily_global_le
    (r : ℕ) (g : P × X → ℝ) (hg : ContDiff ℝ ∞ g) (S : Set X) (hS : IsCompact S)
    (hz : ∀ p z,z ∉ S → g (p,z) = 0) (p : P) (n : ℕ) (C : ℝ) (hC : 0 ≤ C)
    (hJets : ∀ j : Fin (r+1),∀ z : X,
      ‖iteratedFDeriv ℝ n (fun t => iteratedFDeriv ℝ j.val (fun w => g (t,w)) z) p‖ ≤ C) :
    ‖iteratedFDeriv ℝ n (commonSupportClosedCoefficientFamily r g hg S hS hz) p‖ ≤ C := by
  apply norm_iteratedFDeriv_closedCoefficient_of_global_jet_bounds_le r _ p
    (contDiff_commonSupportClosedCoefficientFamily r g hg S hS hz).contDiffAt n C hC
  intro j z
  exact hJets j z

end ShrinkingSpheres
