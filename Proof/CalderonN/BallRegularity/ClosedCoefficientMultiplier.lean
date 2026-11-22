module

public import Proof.CalderonN.BallRegularity.ClosedCoefficientJets
public import Proof.CalderonN.BallRegularity.CoefficientMultiplier
public import Mathlib.Analysis.Normed.Operator.Extend
/-! From Proof/Archive/ClosedCoefficientMultiplier.lean in the Proposition 5.3 release
`f308cb9d8751b6590c8caa28736de77e063a41e1af8cad4e9dfa94819a8299b8`. Module layout adapted for Leanflow v2. -/

@[expose] public section


set_option autoImplicit false
set_option maxSynthPendingDepth 10
set_option maxHeartbeats 1200000
noncomputable section
open Set
open scoped ContDiff
namespace CalderonN.BallDirichlet

variable {dim : ℕ} [NeZero dim]

def closedCoefficientMultiplierL (hcalc : (FixedSobolevCalculus dim)) (k : ℕ) :
    (ClosedCoefficientJets dim) (k+1) →L[ℝ] (BallSobolev dim) k →L[ℝ] (BallSobolev dim) k :=
  (coefficientMultiplierL hcalc k).extend (smoothCoefficientClosureInclusionL (k+1))

theorem closedCoefficientMultiplierL_eq_on_smooth (hcalc : (FixedSobolevCalculus dim)) (k : ℕ)
    (F : (SmoothCoefficientJets dim) (k+1)) :
    closedCoefficientMultiplierL hcalc k (smoothCoefficientClosureInclusionL (k+1) F) =
      coefficientMultiplier hcalc k F := by
  exact (coefficientMultiplierL hcalc k).extend_eq
    (denseRange_smoothCoefficientClosureInclusionL dim (k+1))
    ((show Isometry (smoothCoefficientClosureInclusionL (k+1)) from fun _ _ => rfl).isUniformInducing) F

theorem norm_closedCoefficientMultiplierL_apply_le (hcalc : (FixedSobolevCalculus dim)) (k : ℕ)
    (F : (ClosedCoefficientJets dim) (k+1)) :
    ‖closedCoefficientMultiplierL hcalc k F‖ ≤ sobolevMultiplierBound hcalc k * ‖F‖ := by
  have hm : ∀ G ∈ range (smoothCoefficientClosureInclusionL (k+1)),
      ‖closedCoefficientMultiplierL hcalc k G‖ ≤ sobolevMultiplierBound hcalc k * ‖G‖ := by
    rintro _ ⟨G,rfl⟩
    rw [closedCoefficientMultiplierL_eq_on_smooth,norm_smoothCoefficientClosureInclusionL]
    exact norm_coefficientMultiplier_le hcalc k G
  exact (denseRange_smoothCoefficientClosureInclusionL dim (k+1)).induction hm
    (isClosed_le (by fun_prop) (by fun_prop)) F

variable {H : Type} [NormedAddCommGroup H] [NormedSpace ℝ H] [FiniteDimensional ℝ H]

theorem contDiff_commonSupport_actual_coefficientMultiplier
    (hcalc : (FixedSobolevCalculus dim)) (k : ℕ) (g : H × (X dim) → ℝ)
    (hg : ContDiff ℝ ∞ g) (K : Set (X dim)) (hK : IsCompact K)
    (hz : ∀ t x, x ∉ K → g (t,x) = 0) :
    ContDiff ℝ ∞ (fun t => coefficientMultiplier hcalc k
      (commonSupportCoefficientFamily (k+1) g hg K hK hz t)) := by
  have he : (fun t => coefficientMultiplier hcalc k
      (commonSupportCoefficientFamily (k+1) g hg K hK hz t)) =
      fun t => closedCoefficientMultiplierL hcalc k
        (commonSupportClosedCoefficientFamily (k+1) g hg K hK hz t) := by
    funext t
    exact (closedCoefficientMultiplierL_eq_on_smooth hcalc k _).symm
  rw [he]
  exact (closedCoefficientMultiplierL hcalc k).contDiff.comp
    (contDiff_commonSupportClosedCoefficientFamily (k+1) g hg K hK hz)
end CalderonN.BallDirichlet
