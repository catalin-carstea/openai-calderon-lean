module

public import Proof.CalderonN.CommonSupportMultiplierHigherJets
public import Proof.CalderonN.ClosedLocalZeroMultiplier

/-! Adapted from CommonSupportMultiplierHigherJets in the checked Proposition 5.3 release f308cb9d. -/

public section

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter
open scoped ContDiff BoundedContinuousFunction Topology
namespace CalderonN
open BallDirichlet

variable {dim : ℕ} [NeZero dim]

variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]

/-- All native L2 multiplier jets use the local zeroth spatial coefficient
    jet only. In particular a quadratic coefficient remainder keeps its gain. -/
theorem norm_iteratedFDeriv_commonSupport_coefficientMultiplier_zero_le
    (hcalc : (FixedSobolevCalculus dim)) (g : P × (X dim) → ℝ) (hg : ContDiff ℝ ∞ g)
    (K : Set (X dim)) (hK : IsCompact K) (hz : ∀ p z,z ∉ K → g (p,z) = 0)
    (p : P) (n : ℕ) (q : ℝ) (hq : 0 ≤ q)
    (hJet : ∀ x ∈ (fixedBallOpens dim:Set (X dim)),
      ‖iteratedFDeriv ℝ n (fun t => iteratedFDeriv ℝ 0 (fun z => g (t,z)) x) p‖ ≤ q) :
    ‖iteratedFDeriv ℝ n (fun t => coefficientMultiplier hcalc 0
      (commonSupportCoefficientFamily 1 g hg K hK hz t)) p‖ ≤ q := by
  let F := commonSupportClosedCoefficientFamily 1 g hg K hK hz
  have hF : ContDiffAt ℝ ∞ F p := (contDiff_commonSupportClosedCoefficientFamily 1 g hg K hK hz).contDiffAt
  have hEq : (fun t => coefficientMultiplier hcalc 0
      (commonSupportCoefficientFamily 1 g hg K hK hz t)) = closedCoefficientMultiplierL hcalc 0 ∘ F := by
    funext t
    exact (closedCoefficientMultiplierL_eq_on_smooth hcalc 0 _).symm
  rw [hEq,(closedCoefficientMultiplierL hcalc 0).iteratedFDeriv_comp_left hF (i:=n) (by simp)]
  apply ContinuousMultilinearMap.opNorm_le_bound hq
  intro v
  change ‖closedCoefficientMultiplierL hcalc 0 (iteratedFDeriv ℝ n F p v)‖ ≤ q*∏ i,‖v i‖
  apply norm_closedCoefficientMultiplier_zero_le_of_local_jet hcalc _ (q*∏ i,‖v i‖) (by positivity)
  intro x
  rw [iteratedFDeriv_commonSupportClosedCoefficientFamily_jet_eval]
  exact ((iteratedFDeriv ℝ n (fun t => iteratedFDeriv ℝ 0 (fun z => g (t,z)) x) p).le_opNorm v).trans
    (mul_le_mul_of_nonneg_right (hJet x x.property) (Finset.prod_nonneg (fun _ _ => norm_nonneg _)))

end CalderonN
