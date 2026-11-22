module

public import Proof.CalderonN.ClosedLocalCoefficientJets

import Mathlib.Tactic

/-! Adapted from `Proof/CommonSupportMultiplierDerivative.lean` in the Proposition 5.3 release
`f308cb9d8751b6590c8caa28736de77e063a41e1af8cad4e9dfa94819a8299b8`. -/

public section

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter
open scoped ContDiff BoundedContinuousFunction Topology
namespace CalderonN

open BallDirichlet

variable {dim : ℕ} [NeZero dim]


/-- Evaluation of a genuine coefficient jet is a bounded linear functional,
    also on the closed coefficient space. -/
def closedCoefficientJetEvaluationL (r : ℕ) (j : Fin (r+1)) (x : (X dim)) :
    ClosedCoefficientJets dim r →L[ℝ] ContinuousMultilinearMap ℝ (fun _ : Fin j.val => (X dim)) ℝ :=
  (BoundedContinuousFunction.evalCLM ℝ x).comp
    ((ContinuousLinearMap.proj j).comp (smoothCoefficientJetSubmodule dim r).topologicalClosure.subtypeL)

theorem closedCoefficientJetEvaluationL_apply (r : ℕ) (j : Fin (r+1)) (x : X dim)
    (F : ClosedCoefficientJets dim r) : closedCoefficientJetEvaluationL r j x F = F.val j x := by
  unfold closedCoefficientJetEvaluationL
  rfl

variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]

lemma fderiv_commonSupportClosedCoefficientFamily_jet_eval (r : ℕ)
    (g : P × (X dim) → ℝ) (hg : ContDiff ℝ ∞ g) (K : Set (X dim)) (hK : IsCompact K)
    (hz : ∀ p z,z ∉ K → g (p,z) = 0) (p b : P) (j : Fin (r+1)) (x : (X dim)) :
    (fderiv ℝ (commonSupportClosedCoefficientFamily r g hg K hK hz) p b).val j x =
      fderiv ℝ (fun q => iteratedFDeriv ℝ j.val (fun z => g (q,z)) x) p b := by
  have hF := (contDiff_commonSupportClosedCoefficientFamily r g hg K hK hz).differentiable (by simp) p
  have hD := ((closedCoefficientJetEvaluationL r j x).hasFDerivAt.comp p hF.hasFDerivAt).fderiv
  have hEq : (fun q => closedCoefficientJetEvaluationL r j x
      (commonSupportClosedCoefficientFamily r g hg K hK hz q)) =
      fun q => iteratedFDeriv ℝ j.val (fun z => g (q,z)) x := by
    funext q
    rfl
  simp only [Function.comp_def] at hD
  rw [hEq] at hD
  exact (congrArg (fun L => L b) hD).symm

/-- Uniform bounds for the actual parameter derivatives of just the value
    and first spatial jet control the genuine H1 multiplier derivative. -/
theorem norm_fderiv_commonSupport_coefficientMultiplier_one_le
    (hcalc : FixedSobolevCalculus dim) (g : P × (X dim) → ℝ) (hg : ContDiff ℝ ∞ g)
    (K : Set (X dim)) (hK : IsCompact K) (hz : ∀ p z,z ∉ K → g (p,z) = 0)
    (p : P) (q : ℝ) (hq : 0 ≤ q)
    (hJets : ∀ j : Fin 2,∀ x ∈ ((fixedBallOpens dim):Set (X dim)),
      ‖fderiv ℝ (fun t => iteratedFDeriv ℝ j.val (fun z => g (t,z)) x) p‖ ≤ q) :
    ‖fderiv ℝ (fun t => coefficientMultiplier hcalc 1
      (commonSupportCoefficientFamily 2 g hg K hK hz t)) p‖ ≤ 4*q := by
  let F := commonSupportClosedCoefficientFamily 2 g hg K hK hz
  have hF := (contDiff_commonSupportClosedCoefficientFamily 2 g hg K hK hz).differentiable (by simp) p
  have hEq : (fun t => coefficientMultiplier hcalc 1
      (commonSupportCoefficientFamily 2 g hg K hK hz t)) =
      fun t => closedCoefficientMultiplierL hcalc 1 (F t) := by
    funext t
    exact (closedCoefficientMultiplierL_eq_on_smooth hcalc 1 _).symm
  rw [hEq]
  have hD := ((closedCoefficientMultiplierL hcalc 1).hasFDerivAt.comp p hF.hasFDerivAt).fderiv
  simp only [Function.comp_def] at hD
  dsimp only [F]
  rw [hD]
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro b
  change ‖closedCoefficientMultiplierL hcalc 1 (fderiv ℝ F p b)‖ ≤ (4*q)*‖b‖
  have hLow (j : Fin 2) (x : (fixedBallOpens dim)) :
      ‖(fderiv ℝ F p b).val ⟨j.val,by omega⟩ x‖ ≤ q*‖b‖ := by
    rw [fderiv_commonSupportClosedCoefficientFamily_jet_eval]
    exact (ContinuousLinearMap.le_opNorm _ _).trans
      (mul_le_mul_of_nonneg_right (hJets j x x.property) (norm_nonneg b))
  exact (norm_closedCoefficientMultiplier_one_le_of_local_jets hcalc _ (q*‖b‖)
    (by positivity) (hLow ⟨0,by omega⟩) (hLow ⟨1,by omega⟩)).trans_eq (by ring)

end CalderonN
