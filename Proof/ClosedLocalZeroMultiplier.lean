import Proof.ClosedLocalCoefficientJets
import Proof.CommonSupportMultiplierDerivative
import Mathlib.MeasureTheory.Function.LpSpace.Basic

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter MeasureTheory
open scoped ContDiff ENNReal Topology BoundedContinuousFunction
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.EnergyBridge OAI.AnisotropicCalderon.DirichletFamily

/-- The actual L2 multiplier needs only the local coefficient value on the
    physical ball. No spatial derivative or exterior cutoff norm enters. -/
theorem norm_coefficientMultiplier_zero_le (hcalc : FixedSobolevCalculus)
    (F : SmoothCoefficientJets 1) (q : ℝ) (hq : 0 ≤ q)
    (hValue : ∀ x ∈ (ballOpens:Set X),|coefficientValue 1 F x| ≤ q) :
    ‖coefficientMultiplier hcalc 0 F‖ ≤ q := by
  apply ContinuousLinearMap.opNorm_le_bound _ hq
  intro u
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  have hv := coefficientMultiplier_value_ae hcalc 0 F u
  simp only [TauCeti.Wkp.value_zero] at hv
  filter_upwards [hv,ae_restrict_mem ballOpens.isOpen.measurableSet] with x hx hxB
  rw [hx,Real.norm_eq_abs,abs_mul]
  exact mul_le_mul_of_nonneg_right (hValue x hxB) (abs_nonneg _)

/-- The sharp local L2 multiplier bound passes to the closed coefficient
    completion, using only its true zeroth jet restricted to the unit ball. -/
theorem norm_closedCoefficientMultiplier_zero_local_le (hcalc : FixedSobolevCalculus)
    (F : ClosedCoefficientJets 1) :
    ‖closedCoefficientMultiplierL hcalc 0 F‖ ≤ ‖closedCoefficientLocalJetL 1 ⟨0,by omega⟩ F‖ := by
  have hDense : ∀ G ∈ range (smoothCoefficientClosureInclusionL 1),
      ‖closedCoefficientMultiplierL hcalc 0 G‖ ≤ ‖closedCoefficientLocalJetL 1 ⟨0,by omega⟩ G‖ := by
    rintro _ ⟨G,rfl⟩
    rw [closedCoefficientMultiplierL_eq_on_smooth]
    let J := closedCoefficientLocalJetL 1 ⟨0,by omega⟩ (smoothCoefficientClosureInclusionL 1 G)
    apply norm_coefficientMultiplier_zero_le hcalc G ‖J‖ (norm_nonneg _)
    intro x hx
    have h := J.norm_coe_le_norm ⟨x,hx⟩
    change ‖G.val ⟨0,by omega⟩ x‖ ≤ ‖J‖ at h
    rw [coefficientJet_eq_iteratedFDeriv,norm_iteratedFDeriv_zero] at h
    exact h
  exact (denseRange_smoothCoefficientClosureInclusionL 1).induction hDense
    (isClosed_le (by fun_prop) (by fun_prop)) F

theorem norm_closedCoefficientMultiplier_zero_le_of_local_jet (hcalc : FixedSobolevCalculus)
    (F : ClosedCoefficientJets 1) (q : ℝ) (hq : 0 ≤ q)
    (h0 : ∀ x : ballOpens,‖F.val ⟨0,by omega⟩ x‖ ≤ q) :
    ‖closedCoefficientMultiplierL hcalc 0 F‖ ≤ q :=
  (norm_closedCoefficientMultiplier_zero_local_le hcalc F).trans ((BoundedContinuousFunction.norm_le hq).mpr h0)

variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]

/-- The actual L2 multiplier derivative is controlled by the true local
    parameter derivative of the zeroth coefficient jet alone. -/
theorem norm_fderiv_commonSupport_coefficientMultiplier_zero_le
    (hcalc : FixedSobolevCalculus) (g : P × X → ℝ) (hg : ContDiff ℝ ∞ g)
    (K : Set X) (hK : IsCompact K) (hz : ∀ p z,z ∉ K → g (p,z) = 0)
    (p : P) (q : ℝ) (hq : 0 ≤ q)
    (hJet : ∀ x ∈ (ballOpens:Set X),
      ‖fderiv ℝ (fun t => iteratedFDeriv ℝ 0 (fun z => g (t,z)) x) p‖ ≤ q) :
    ‖fderiv ℝ (fun t => coefficientMultiplier hcalc 0
      (commonSupportCoefficientFamily 1 g hg K hK hz t)) p‖ ≤ q := by
  let F := commonSupportClosedCoefficientFamily 1 g hg K hK hz
  have hF := (contDiff_commonSupportClosedCoefficientFamily 1 g hg K hK hz).differentiable (by simp) p
  have hEq : (fun t => coefficientMultiplier hcalc 0
      (commonSupportCoefficientFamily 1 g hg K hK hz t)) =
      fun t => closedCoefficientMultiplierL hcalc 0 (F t) := by
    funext t
    exact (closedCoefficientMultiplierL_eq_on_smooth hcalc 0 _).symm
  rw [hEq]
  have hD := ((closedCoefficientMultiplierL hcalc 0).hasFDerivAt.comp p hF.hasFDerivAt).fderiv
  simp only [Function.comp_def] at hD
  dsimp only [F]
  rw [hD]
  apply ContinuousLinearMap.opNorm_le_bound _ hq
  intro b
  change ‖closedCoefficientMultiplierL hcalc 0 (fderiv ℝ F p b)‖ ≤ q*‖b‖
  apply norm_closedCoefficientMultiplier_zero_le_of_local_jet hcalc _ (q*‖b‖) (by positivity)
  intro x
  rw [fderiv_commonSupportClosedCoefficientFamily_jet_eval]
  exact (ContinuousLinearMap.le_opNorm _ _).trans
    (mul_le_mul_of_nonneg_right (hJet x x.property) (norm_nonneg b))

end ShrinkingSpheres
