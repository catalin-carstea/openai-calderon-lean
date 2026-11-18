import Proof.CommonSupportMultiplierDerivative
import Proof.ClosedLocalZeroMultiplier

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter
open scoped ContDiff BoundedContinuousFunction Topology
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.EnergyBridge OAI.AnisotropicCalderon.DirichletFamily

variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]

lemma iteratedFDeriv_commonSupportClosedCoefficientFamily_jet_eval (r : ℕ)
    (g : P × X → ℝ) (hg : ContDiff ℝ ∞ g) (K : Set X) (hK : IsCompact K)
    (hz : ∀ p z,z ∉ K → g (p,z) = 0) (p : P) (n : ℕ) (v : Fin n → P)
    (j : Fin (r+1)) (x : X) :
    (iteratedFDeriv ℝ n (commonSupportClosedCoefficientFamily r g hg K hK hz) p v).val j x =
      iteratedFDeriv ℝ n (fun q => iteratedFDeriv ℝ j.val (fun z => g (q,z)) x) p v := by
  let F := commonSupportClosedCoefficientFamily r g hg K hK hz
  have hF : ContDiffAt ℝ ∞ F p := (contDiff_commonSupportClosedCoefficientFamily r g hg K hK hz).contDiffAt
  have hComp := (closedCoefficientJetEvaluationL r j x).iteratedFDeriv_comp_left hF (i:=n) (by simp)
  have hEq : (closedCoefficientJetEvaluationL r j x) ∘ F =
      (fun q => iteratedFDeriv ℝ j.val (fun z => g (q,z)) x) := by funext q;rfl
  rw [hEq] at hComp
  have hEval := congrArg (fun A : ContinuousMultilinearMap ℝ (fun _ : Fin n => P)
      (ContinuousMultilinearMap ℝ (fun _ : Fin j.val => X) ℝ) => A v) hComp
  exact hEval.symm

/-- Higher native H1 multiplier jets need only the corresponding local
    value/first-spatial coefficient jets, even though the smooth family
    is represented by a globally compact extension. -/
theorem norm_iteratedFDeriv_commonSupport_coefficientMultiplier_one_le
    (hcalc : FixedSobolevCalculus) (g : P × X → ℝ) (hg : ContDiff ℝ ∞ g)
    (K : Set X) (hK : IsCompact K) (hz : ∀ p z,z ∉ K → g (p,z) = 0)
    (p : P) (n : ℕ) (q : ℝ) (hq : 0 ≤ q)
    (hJets : ∀ j : Fin 2,∀ x ∈ (ballOpens:Set X),
      ‖iteratedFDeriv ℝ n (fun t => iteratedFDeriv ℝ j.val (fun z => g (t,z)) x) p‖ ≤ q) :
    ‖iteratedFDeriv ℝ n (fun t => coefficientMultiplier hcalc 1
      (commonSupportCoefficientFamily 2 g hg K hK hz t)) p‖ ≤ 4*q := by
  let F := commonSupportClosedCoefficientFamily 2 g hg K hK hz
  have hF : ContDiffAt ℝ ∞ F p := (contDiff_commonSupportClosedCoefficientFamily 2 g hg K hK hz).contDiffAt
  have hEq : (fun t => coefficientMultiplier hcalc 1
      (commonSupportCoefficientFamily 2 g hg K hK hz t)) = closedCoefficientMultiplierL hcalc 1 ∘ F := by
    funext t
    exact (closedCoefficientMultiplierL_eq_on_smooth hcalc 1 _).symm
  rw [hEq,(closedCoefficientMultiplierL hcalc 1).iteratedFDeriv_comp_left hF (i:=n) (by simp)]
  apply ContinuousMultilinearMap.opNorm_le_bound (by positivity)
  intro v
  change ‖closedCoefficientMultiplierL hcalc 1 (iteratedFDeriv ℝ n F p v)‖ ≤ (4*q)*∏ i,‖v i‖
  have hLow (j : Fin 2) (x : ballOpens) :
      ‖(iteratedFDeriv ℝ n F p v).val ⟨j.val,by omega⟩ x‖ ≤ q*∏ i,‖v i‖ := by
    rw [iteratedFDeriv_commonSupportClosedCoefficientFamily_jet_eval]
    exact ((iteratedFDeriv ℝ n (fun t => iteratedFDeriv ℝ j.val (fun z => g (t,z)) x) p).le_opNorm v).trans
      (mul_le_mul_of_nonneg_right (hJets j x x.property) (Finset.prod_nonneg (fun _ _ => norm_nonneg _)))
  exact (norm_closedCoefficientMultiplier_one_le_of_local_jets hcalc _ (q*∏ i,‖v i‖)
    (by positivity) (hLow ⟨0,by omega⟩) (hLow ⟨1,by omega⟩)).trans_eq (by ring)

/-- All native L2 multiplier jets use the local zeroth spatial coefficient
    jet only. In particular a quadratic coefficient remainder keeps its gain. -/
theorem norm_iteratedFDeriv_commonSupport_coefficientMultiplier_zero_le
    (hcalc : FixedSobolevCalculus) (g : P × X → ℝ) (hg : ContDiff ℝ ∞ g)
    (K : Set X) (hK : IsCompact K) (hz : ∀ p z,z ∉ K → g (p,z) = 0)
    (p : P) (n : ℕ) (q : ℝ) (hq : 0 ≤ q)
    (hJet : ∀ x ∈ (ballOpens:Set X),
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

end ShrinkingSpheres
