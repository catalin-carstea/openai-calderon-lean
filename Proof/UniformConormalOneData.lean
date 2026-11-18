import Proof.UniformOneBoundaryTaylor
import Proof.ConormalOneData

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3200000
set_option maxSynthPendingDepth 15
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter MeasureTheory
open scoped ENNReal Topology
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.EnergyBridge OAI.AnisotropicCalderon.DirichletFamily
open OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open OAI.AnisotropicCalderon.SphereHarmonic
attribute [local irreducible] nativeWeakConormalEndpoint weakFirstConormalVariationL oneBoundaryCoefficientMulL

/-- Joint actual conormal and normal-inverse H1 Taylor data. The coefficient
    representatives and first variation are shared throughout; neither an
    arbitrary inverse bound nor a fixed-radius family is a premise. -/
theorem uniform_actual_conormal_one_data {Y Ω : Set X} (hΩ : IsOpen Ω)
    {m : ℕ} (hm : 3 ≤ m) (K ρ c₀ : ℝ) (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ)
    (hK : 1 ≤ K) (hρ : 0 < ρ) :
    ∃ η P Q CN2 : ℝ,∃ F0 : SmoothCoefficientMatrix 2,
      0 < η ∧ 0 ≤ P ∧ 0 ≤ Q ∧ 0 ≤ CN2 ∧
      (∀ x ∈ Metric.closedBall (0:X) 2,coefficientMatrixField 2 F0 x = 1) ∧
      ∀ floor,1 ≤ floor → ∀ ε,0 ≤ ε → ε ≤ η → ∀ d,
      Admissible Y Ω K ρ c₀ M Cj floor ε d → ∀ y ∈ Y,
      let a := principalCoefficient (framedNormalMetric d.g₁ d.frame d.expMap y (d.radius y))
      let KP := 4*K^2
      let c := firstMetricDensityFactor d.γ d.g₁ y
      let r := d.radius y
      let ell := firstDensityCenterLinearL d y
      ∃ F F1 : SmoothCoefficientMatrix 2,
      ∃ e : NativeWeakEnergyData a (5*metricDensityBudget KP*KP) (metricDensityBudget KP*KP),
      ∃ ha1 : MemLp (fun x => TauCeti.PDE.energyIntegrand (coefficientMatrixField 2 F1 x) 0 0) ⊤
        ((volume:Measure X).restrict ballOpens),
      ∃ N : SphereSobolev 1 →L[ℝ] SphereSobolev 0,
        (∀ x ∈ Metric.closedBall (0:X) 2,∀ i j,coefficientValue 2 (F i j) =ᶠ[𝓝 x] (fun z => a z i j)) ∧
        (∀ x ∈ Metric.closedBall (0:X) 2,∀ i j,coefficientValue 2 (F1 i j) =ᶠ[𝓝 x] (fun z => ell z*(1:Mat) i j)) ∧
        (strongDirichletOperator fixedSobolevCalculus 0 F).IsInvertible ∧
        (strongDirichletOperator fixedSobolevCalculus 0 (c • F0)).IsInvertible ∧
        TauCeti.PDE.UniformlyEllipticOn (ballOpens:Set X) (coefficientMatrixField 2 F)
          ((metricDensityBudget KP)⁻¹*KP⁻¹) (metricDensityBudget KP*KP) ∧
        (∀ i j,∀ x ∈ (ballOpens:Set X),|coefficientValue 2 (F1 i j) x| ≤ P) ∧
        (∀ i j,∀ x ∈ (ballOpens:Set X),‖fderiv ℝ (coefficientValue 2 (F1 i j)) x‖ ≤ P) ∧
        OneBoundaryTaylorData F F0 F1 c r (2*K) ((73*36)*P) ((73*36)*Q)
          ((2*K)*((73*36)*P+(73*36)*Q)*K)
          ((2*K)*(K*((73*36)*Q)+K^2*((73*36)*P+(73*36)*Q)*((73*36)*P))) ((73*78)*Q) ∧
        ConormalOneData a e.coefficient_bound F1 c r ell N CN2 := by
  obtain ⟨ηB,C,P,Q,F0,hηB,hC,hP,hQ,hF0,hBoundary⟩ :=
    uniform_actual_one_boundary_taylor (Y:=Y) hΩ hm K ρ c₀ M Cj hK hρ
  obtain ⟨ηN,CN2,F0N,hηN,hCN2,hF0N,hConormal⟩ :=
    uniform_actual_midpoint_conormal_taylor (Y:=Y) hΩ hm K ρ c₀ M Cj hK hρ
  refine ⟨min ηB ηN,P,Q,CN2,F0,lt_min hηB hηN,hP,hQ,hCN2,hF0,?_⟩
  intro floor hf ε hε hSmall d hd y hy
  dsimp only
  obtain ⟨F,F1,hRep,hRep1,hInv,hNorm,hInv0,hNorm0,hUE,hV1,hD1,hVR,hDR,hOne⟩ :=
    hBoundary floor hf ε hε (hSmall.trans (min_le_left _ _)) d hd y hy
  have hNHere := hConormal floor hf ε hε (hSmall.trans (min_le_right _ _)) d hd y hy
  dsimp only at hNHere
  obtain ⟨FN,F1N,e,ha1N,R,hRepN,hRep1N,hInvN,hInv0N,hRN,hUpper,hLower,hRS⟩ := hNHere
  let a := principalCoefficient (framedNormalMetric d.g₁ d.frame d.expMap y (d.radius y))
  let c := firstMetricDensityFactor d.γ d.g₁ y
  let r := d.radius y
  let ell := firstDensityCenterLinearL d y
  have hc : 0 < c := firstMetricDensityFactor_pos _ _ _
  have ha1 := memLp_coefficient_energy_of_entry_bound F1 P hP hV1
  have hFirstEq := weakFirstConormal_congr_on_ball c ha1N ha1 (by
    intro x hx
    ext i j
    exact (hRep1N x (unitBall_subset_closedBall_two hx) i j).eq_of_nhds.trans
      (hRep1 x (unitBall_subset_closedBall_two hx) i j).eq_of_nhds.symm)
  have hLowerEq := congrArg (fun L : SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ)) =>
    (nativeWeakConormalEndpoint a 0 0 e.coefficient_bound sphereFischerInner-c • fixedLowRadialL-r • L).comp
      (sphereSobolevInclusionL 1 (1/2:ℝ) (by norm_num))) hFirstEq
  let N := conormalOneFromRemainderL F1 c r ell R
  have hData : ConormalOneData a e.coefficient_bound F1 c r ell N CN2 :=
    conormalOneData_of_remainder e.coefficient_bound F0 F1 c r CN2 hc ell hF0
      (fun x hx i j => (hRep1 x hx i j).eq_of_nhds) ha1 hInv0 R hRN (hLower.trans hLowerEq) hRS
  exact ⟨F,F1,e,ha1,N,hRep,hRep1,hInv,hInv0,hUE,hV1,hD1,hOne,hData⟩

end ShrinkingSpheres
