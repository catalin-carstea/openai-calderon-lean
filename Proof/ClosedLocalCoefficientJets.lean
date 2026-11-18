import Proof.SharpCoefficientMultiplier
import Proof.Archive.ClosedCoefficientMultiplier

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1400000
set_option maxSynthPendingDepth 20
open Set
open scoped ContDiff BoundedContinuousFunction
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.EnergyBridge OAI.AnisotropicCalderon.DirichletFamily

/-- Restrict one genuine closed coefficient jet to the physical open ball.
    Coefficient cutoffs outside the ball never enter this seminorm. -/
def closedCoefficientLocalJetL (r : ℕ) (j : Fin (r+1)) :
    ClosedCoefficientJets r →L[ℝ] (ballOpens →ᵇ ContinuousMultilinearMap ℝ (fun _ : Fin j.val => X) ℝ) :=
  (BoundedContinuousFunction.compContinuousCLM _ ℝ
    ⟨Subtype.val,continuous_subtype_val⟩).comp
      ((ContinuousLinearMap.proj j).comp (smoothCoefficientJetSubmodule r).topologicalClosure.subtypeL)

lemma closedCoefficientLocalJetL_apply (r : ℕ) (j : Fin (r+1))
    (F : ClosedCoefficientJets r) (x : ballOpens) :
    closedCoefficientLocalJetL r j F x = F.val j x := rfl

/-- The supplied closed H1 multiplier is controlled by just its two local
    low jets. This estimate remains valid on the coefficient completion. -/
theorem norm_closedCoefficientMultiplier_one_local_le (hcalc : FixedSobolevCalculus)
    (F : ClosedCoefficientJets 2) :
    ‖closedCoefficientMultiplierL hcalc 1 F‖ ≤
      2*(‖closedCoefficientLocalJetL 2 ⟨0,by omega⟩ F‖+
        ‖closedCoefficientLocalJetL 2 ⟨1,by omega⟩ F‖) := by
  have hDense : ∀ G ∈ range (smoothCoefficientClosureInclusionL 2),
      ‖closedCoefficientMultiplierL hcalc 1 G‖ ≤
        2*(‖closedCoefficientLocalJetL 2 ⟨0,by omega⟩ G‖+
          ‖closedCoefficientLocalJetL 2 ⟨1,by omega⟩ G‖) := by
    rintro _ ⟨G,rfl⟩
    rw [closedCoefficientMultiplierL_eq_on_smooth]
    let J0 := closedCoefficientLocalJetL 2 ⟨0,by omega⟩ (smoothCoefficientClosureInclusionL 2 G)
    let J1 := closedCoefficientLocalJetL 2 ⟨1,by omega⟩ (smoothCoefficientClosureInclusionL 2 G)
    apply norm_coefficientMultiplier_one_le hcalc G (‖J0‖+‖J1‖) (by positivity)
    · intro x hx
      have h := J0.norm_coe_le_norm ⟨x,hx⟩
      change ‖G.val ⟨0,by omega⟩ x‖ ≤ ‖J0‖ at h
      rw [coefficientJet_eq_iteratedFDeriv,norm_iteratedFDeriv_zero] at h
      have hVal : |coefficientValue 2 G x| ≤ ‖J0‖ := by simpa only [Real.norm_eq_abs] using h
      exact hVal.trans (le_add_of_nonneg_right (norm_nonneg J1))
    · intro x hx
      have h := J1.norm_coe_le_norm ⟨x,hx⟩
      change ‖G.val ⟨1,by omega⟩ x‖ ≤ ‖J1‖ at h
      rw [coefficientJet_eq_iteratedFDeriv,norm_iteratedFDeriv_one] at h
      exact h.trans (le_add_of_nonneg_left (norm_nonneg J0))
  exact (denseRange_smoothCoefficientClosureInclusionL 2).induction hDense
    (isClosed_le (by fun_prop) (by fun_prop)) F

/-- Pointwise local low-jet bounds therefore control the actual completed
    multiplier, including derivatives of a smooth common-support family. -/
theorem norm_closedCoefficientMultiplier_one_le_of_local_jets (hcalc : FixedSobolevCalculus)
    (F : ClosedCoefficientJets 2) (q : ℝ) (hq : 0 ≤ q)
    (h0 : ∀ x : ballOpens,‖F.val ⟨0,by omega⟩ x‖ ≤ q)
    (h1 : ∀ x : ballOpens,‖F.val ⟨1,by omega⟩ x‖ ≤ q) :
    ‖closedCoefficientMultiplierL hcalc 1 F‖ ≤ 4*q := by
  have hJ0 : ‖closedCoefficientLocalJetL 2 ⟨0,by omega⟩ F‖ ≤ q :=
    (BoundedContinuousFunction.norm_le hq).mpr h0
  have hJ1 : ‖closedCoefficientLocalJetL 2 ⟨1,by omega⟩ F‖ ≤ q :=
    (BoundedContinuousFunction.norm_le hq).mpr h1
  exact (norm_closedCoefficientMultiplier_one_local_le hcalc F).trans (by linarith)

end ShrinkingSpheres
