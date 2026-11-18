import Proof.OrderOneNormalInverse
import Proof.UniformFirstStrongTaylorData

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2600000
set_option maxSynthPendingDepth 15
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter MeasureTheory
open scoped ENNReal Topology
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.EnergyBridge OAI.AnisotropicCalderon.DirichletFamily
open OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open OAI.AnisotropicCalderon.SphereHarmonic
attribute [local irreducible] oneBoundaryCoefficientMulL

/-- Actual shared compact coefficient witnesses with a uniformly controlled
    H1 normal inverse, its quadratic Taylor error, and quadratic tangential
    coefficients. Only the already proved local C1 geometric bounds enter. -/
theorem uniform_actual_one_boundary_taylor {Y Ω : Set X} (hΩ : IsOpen Ω)
    {m : ℕ} (hm : 3 ≤ m) (K ρ c₀ : ℝ) (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ)
    (hK : 1 ≤ K) (hρ : 0 < ρ) :
    ∃ η C P Q : ℝ,∃ F0 : SmoothCoefficientMatrix 2,
      0 < η ∧ 0 ≤ C ∧ 0 ≤ P ∧ 0 ≤ Q ∧
      (∀ x ∈ Metric.closedBall (0:X) 2,coefficientMatrixField 2 F0 x = 1) ∧
      ∀ floor,1 ≤ floor → ∀ ε,0 ≤ ε → ε ≤ η → ∀ d,
      Admissible Y Ω K ρ c₀ M Cj floor ε d → ∀ y ∈ Y,
      let a := principalCoefficient (framedNormalMetric d.g₁ d.frame d.expMap y (d.radius y))
      let KP := 4*K^2
      let c := firstMetricDensityFactor d.γ d.g₁ y
      let r := d.radius y
      let ell := firstDensityCenterLinearL d y
      ∃ F F1 : SmoothCoefficientMatrix 2,
        (∀ x ∈ Metric.closedBall (0:X) 2,∀ i j,coefficientValue 2 (F i j) =ᶠ[𝓝 x] (fun z => a z i j)) ∧
        (∀ x ∈ Metric.closedBall (0:X) 2,∀ i j,coefficientValue 2 (F1 i j) =ᶠ[𝓝 x] (fun z => ell z*(1:Mat) i j)) ∧
        (strongDirichletOperator fixedSobolevCalculus 0 F).IsInvertible ∧
        ‖(strongDirichletOperator fixedSobolevCalculus 0 F).inverse‖ ≤ C ∧
        (strongDirichletOperator fixedSobolevCalculus 0 (c • F0)).IsInvertible ∧
        ‖(strongDirichletOperator fixedSobolevCalculus 0 (c • F0)).inverse‖ ≤ C ∧
        TauCeti.PDE.UniformlyEllipticOn (ballOpens:Set X) (coefficientMatrixField 2 F)
          ((metricDensityBudget KP)⁻¹*KP⁻¹) (metricDensityBudget KP*KP) ∧
        (∀ i j,∀ x ∈ (ballOpens:Set X),|coefficientValue 2 (F1 i j) x| ≤ P) ∧
        (∀ i j,∀ x ∈ (ballOpens:Set X),‖fderiv ℝ (coefficientValue 2 (F1 i j)) x‖ ≤ P) ∧
        (∀ i j,∀ x ∈ (ballOpens:Set X),|coefficientValue 2 ((F-c • F0-r • F1) i j) x| ≤ Q*r^2) ∧
        (∀ i j,∀ x ∈ (ballOpens:Set X),‖fderiv ℝ (coefficientValue 2 ((F-c • F0-r • F1) i j)) x‖ ≤ Q*r^2) ∧
        OneBoundaryTaylorData F F0 F1 c r (2*K) ((73*36)*P) ((73*36)*Q)
          ((2*K)*((73*36)*P+(73*36)*Q)*K)
          ((2*K)*(K*((73*36)*Q)+K^2*((73*36)*P+(73*36)*Q)*((73*36)*P))) ((73*78)*Q) := by
  obtain ⟨ηS,C,P,Q,F0,hηS,hC,hP,hQ,hF0,hStrong⟩ :=
    uniform_first_strong_taylor_data (Y:=Y) hΩ hm K ρ c₀ M Cj hK hρ
  obtain ⟨ηE,hηE,hElliptic⟩ := uniform_enlarged_framed_normal_elliptic
    (Y:=Y) hΩ (by omega) K ρ c₀ M Cj hK hρ 2 (by norm_num)
  let D := (73*36)*P+(73*36)*Q
  let δ := 1/(2*K*D+1)
  have hKpos : 0 < K := zero_lt_one.trans_le hK
  have hD : 0 ≤ D := by dsimp [D];positivity
  have hδ : 0 < δ := by dsimp [δ];positivity
  refine ⟨min (min ηS ηE) (min 1 δ),C,P,Q,F0,lt_min (lt_min hηS hηE) (lt_min zero_lt_one hδ),hC,hP,hQ,hF0,?_⟩
  intro floor hf ε hε hSmall d hd y hy
  dsimp only
  obtain ⟨F,F1,hRep,hRep1,hInv,hNorm,hInv0,hNorm0,hVal1,hDeriv1,hValR,hDerivR⟩ :=
    hStrong floor hf ε hε (hSmall.trans ((min_le_left _ _).trans (min_le_left _ _))) d hd y hy
  let c := firstMetricDensityFactor d.γ d.g₁ y
  let r := d.radius y
  let KP := 4*K^2
  let ell := firstDensityCenterLinearL d y
  have hr : 0 < r := (hd.2.2.2.2.1.2 y hy).1
  have hrε := (radius_bounds r (beta d.γ d.radius y) floor ε hr.le hf
    (hd.2.2.2.2.1.2 y hy).2.1 (hd.2.2.2.2.2 y hy).2).2.2
  have hr1 : r ≤ 1 := hrε.trans (hSmall.trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hc : 0 < c := firstMetricDensityFactor_pos _ _ _
  have hci : c⁻¹ ≤ K := hd.1.firstMetricDensityFactor_inverse_le hKpos (hd.2.1.center_mem hy)
  have hScalar (w : UnitSphere) : coefficientMatrixField 2 F1 w.val = ell w.val • (1:Mat) := by
    have hw := Metric.closedBall_subset_closedBall (by norm_num : (1:ℝ) ≤ 2) (Metric.sphere_subset_closedBall w.property)
    ext i j
    exact (hRep1 w.val hw i j).eq_of_nhds
  have hEll := hElliptic floor hf ε hε (hSmall.trans ((min_le_left _ _).trans (min_le_right _ _))) d hd y hy d.g₁ (by simp)
  have hKP : 1 ≤ KP := by dsimp [KP];nlinarith only [hK,sq_nonneg (K-1)]
  have hUE := ((hEll.principalCoefficient_tau hKP).mono_set unitBall_subset_closedBall_two).congr
    (show ∀ x ∈ (ballOpens:Set X),coefficientMatrixField 2 F x =
      principalCoefficient (framedNormalMetric d.g₁ d.frame d.expMap y r) x by
      intro x hx
      ext i j
      exact (hRep x (unitBall_subset_closedBall_two hx) i j).eq_of_nhds)
  have hSmallr : K*D*r ≤ (1/2:ℝ) := by
    have hεD : ε*(2*K*D+1) ≤ 1 :=
      (le_div_iff₀ (show 0 < 2*K*D+1 by positivity)).mp
        (hSmall.trans ((min_le_right _ _).trans (min_le_right _ _)))
    have hR := mul_le_mul_of_nonneg_left hrε (mul_nonneg hKpos.le hD)
    nlinarith only [hεD,hR,hε]
  exact ⟨F,F1,hRep,hRep1,hInv,hNorm,hInv0,hNorm0,hUE,hVal1,hDeriv1,hValR,hDerivR,
    one_boundary_taylor_data_of_local_C1 F F0 F1 c r K P Q _ _ hc hKpos.le hci hr.le hr1 hP hQ ell
      hF0 hScalar hUE hVal1 hDeriv1 hValR hDerivR hSmallr⟩

end ShrinkingSpheres
