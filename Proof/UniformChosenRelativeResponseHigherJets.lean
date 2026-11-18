import Proof.ChosenRelativeResponseHigherJets
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3800000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter
open scoped ContDiff Topology
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.EnergyBridge OAI.AnisotropicCalderon.DirichletFamily
open OAI.AnisotropicCalderon.SphereHarmonic

/-- All finite forward/adjoint joint jets are uniform for ANY previously
    chosen native packet with the same admitted geometry and uniform inverse
    budgets. The constants precede every radius profile and representative. -/
theorem uniform_chosen_relative_forward_adjoint_higher_jets {Y Ω : Set X}
    (hY : IsOpen Y) (hΩ : IsOpen Ω) {m : ℕ} (N : ℕ) (hNm : N+5 ≤ m)
    (K ρ c₀ : ℝ) (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ) (hK : 1 ≤ K) (hρ : 0 < ρ)
    (CI CW : ℝ) (hCI : 0 ≤ CI) (hCW : 0 ≤ CW)
    (F0 : SmoothCoefficientMatrix 2)
    (hF0 : ∀ z ∈ Metric.closedBall (0:X) 2,coefficientMatrixField 2 F0 z = 1) :
    ∃ η CF CA : ℝ,0 < η ∧ η ≤ 1 ∧ 1 ≤ CF ∧ 1 ≤ CA ∧
      ∀ floor,1 ≤ floor → ∀ ε,0 ≤ ε → ε ≤ η → ∀ d,
      Admissible Y Ω K ρ c₀ M Cj floor ε d → ∀ y ∈ Y,∀ N0 : ℕ,∀ C0 : ℝ,
      ∀ q : NormalFrameRelativeCoefficientJetFamily Y Ω d.γ d.g₁ d.expMap y
        (frameVectorLinear d.frame y) (d.radius y) N0 2 C0,
      NormalFrameRelativeNativePointData q F0 CI CW →
      ∀ t : NormalFrameRelativeResponsePacket q,
        (∀ n : ℕ,n ≤ N → ‖iteratedFDeriv ℝ n t.forwardTaylor ((y,frameVectorLinear d.frame y),0)‖ ≤ CF*(d.radius y)^2) ∧
        (∀ n : ℕ,n ≤ N → ‖iteratedFDeriv ℝ n t.adjointTaylor ((y,frameVectorLinear d.frame y),0)‖ ≤ CA*(d.radius y)^2) := by
  obtain ⟨ηG,C,hηG,hηG1,hC,hBudget⟩ := uniform_chosen_relative_coefficient_higher_budget
    hY hΩ (N+1) (by omega) K ρ c₀ M Cj hK hρ 2 (by norm_num)
  let D := 18*coarseOneBoundaryBundleBudget*C
  have hD : 0 ≤ D := by
    have hCB := coarseOneBoundaryBundleBudget_nonneg
    have hC0 : 0 ≤ C := zero_le_one.trans hC
    dsimp only [D]
    positivity
  let ηS := (4*(D+1))⁻¹
  have hηS : 0 < ηS := by dsimp only [ηS];positivity
  let BF := normalFrameRelativeMidpointJetBudget N CI CW C
  let BA := normalFrameRelativeAdjointHigherJetBudget N C BF
  refine ⟨min ηG (min 1 ηS),1+|BF|,1+|BA|,lt_min hηG (lt_min zero_lt_one hηS),
    (min_le_right _ _).trans (min_le_left _ _),by linarith [abs_nonneg BF],by linarith [abs_nonneg BA],?_⟩
  intro floor hf ε hε hSmall d hd y hy N0 C0 q point t
  have hr := (hd.2.2.2.2.1.2 y hy).1
  have hrε : d.radius y ≤ ε := (radius_bounds (d.radius y) (beta d.γ d.radius y) floor ε hr.le hf
    (hd.2.2.2.2.1.2 y hy).2.1 (hd.2.2.2.2.2 y hy).2).2.2
  have hr1 : d.radius y ≤ 1 := hrε.trans (hSmall.trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hrS : d.radius y ≤ ηS := hrε.trans (hSmall.trans ((min_le_right _ _).trans (min_le_right _ _)))
  have hSmallR : (2*(18*coarseOneBoundaryBundleBudget)*C)*d.radius y ≤ (1/2:ℝ) := by
    have hden : 0 < 4*(D+1) := by positivity
    have hFrac : (2*D)/(4*(D+1)) ≤ (1/2:ℝ) := (div_le_iff₀ hden).mpr (by nlinarith only [hD])
    have hb : (2*D)*d.radius y ≤ (2*D)/(4*(D+1)) := by
      simpa only [ηS,div_eq_mul_inv] using mul_le_mul_of_nonneg_left hrS (by positivity : 0 ≤ 2*D)
    exact (show (2*(18*coarseOneBoundaryBundleBudget)*C)*d.radius y = (2*D)*d.radius y by dsimp only [D];ring).le.trans (hb.trans hFrac)
  have hB := hBudget floor hf ε hε (hSmall.trans (min_le_left _ _)) d hd y hy N0 C0 q
  have hForward := t.forward_higher_jets_of_budget N C CI CW hB (by norm_num) (zero_le_one.trans hC)
    hCI hCW hr.le hr1 F0 hF0 point
  have hAdjoint := t.adjoint_higher_jets_of_budget N C CI CW hB (by norm_num) (zero_le_one.trans hC)
    hCI hCW hr.le hr1 F0 hF0 point hSmallR
  constructor
  · intro n hn
    exact (hForward n hn).trans (mul_le_mul_of_nonneg_right ((le_abs_self BF).trans (by linarith)) (sq_nonneg _))
  · intro n hn
    exact (hAdjoint n hn).trans (mul_le_mul_of_nonneg_right ((le_abs_self BA).trans (by linarith)) (sq_nonneg _))

end ShrinkingSpheres
