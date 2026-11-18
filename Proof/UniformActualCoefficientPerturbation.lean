import Proof.UniformActualStrongInverse

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxSynthPendingDepth 15
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter MeasureTheory
open scoped ContDiff Topology ENNReal
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.EnergyBridge OAI.AnisotropicCalderon.DirichletFamily

/-- A genuine coefficient representative with a locally small flat perturbation.
    The exterior compact extension is not required to have small higher jets. -/
def LocalFlatCoefficientComparison (a : X → Mat) (F0 : SmoothCoefficientMatrix 2) (q : ℝ) : Prop :=
  ∃ F : SmoothCoefficientMatrix 2,∃ c : ℝ,0 < c ∧
    (∀ x ∈ Metric.closedBall (0:X) 2,∀ i j,
      coefficientValue 2 (F i j) =ᶠ[𝓝 x] (fun z => a z i j)) ∧
    (∀ i j,∀ x ∈ (ballOpens : Set X),|coefficientValue 2 ((F-c • F0) i j) x| ≤ q) ∧
    (∀ i j,∀ x ∈ (ballOpens : Set X),‖fderiv ℝ (coefficientValue 2 ((F-c • F0) i j)) x‖ ≤ q)

/-- Uniform radius-linear local coefficient perturbations, retaining the common
    fixed flat representative for downstream H2 forcing estimates. -/
theorem uniform_actual_local_flat_comparison {Y Ω : Set X} (hΩ : IsOpen Ω)
    {m : ℕ} (hm : 3 ≤ m) (K ρ c₀ : ℝ) (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ)
    (hK : 1 ≤ K) (hρ : 0 < ρ) :
    ∃ η Q : ℝ,∃ F0 : SmoothCoefficientMatrix 2,0 < η ∧ 0 ≤ Q ∧
      (∀ x ∈ Metric.closedBall (0:X) 2,coefficientMatrixField 2 F0 x = 1) ∧
      ∀ floor,1 ≤ floor → ∀ ε,0 ≤ ε → ε ≤ η → ∀ d,
      Admissible Y Ω K ρ c₀ M Cj floor ε d → ∀ y ∈ Y,
      LocalFlatCoefficientComparison
        (principalCoefficient (framedNormalMetric d.g₁ d.frame d.expMap y (d.radius y))) F0 (Q*d.radius y) := by
  let N0 := normalPrincipalClosenessBudget (by omega : 2 ≤ m) K M 2
  let N1 := normalCoefficientAngularDerivativeBudget hm K M
  have hN0 : 0 ≤ N0 := by
    dsimp [N0,normalPrincipalClosenessBudget,normalMetricClosenessBudget,normalVariationErrorBudget,
      backgroundConnectionDerivativeBudget,metricDensityBudget]
    positivity
  have hN1 : 0 ≤ N1 := by
    dsimp [N1,normalCoefficientAngularDerivativeBudget,normalMetricAngularDerivativeBudget,
      backgroundSecondNormalVariationBudget,secondNormalVariationBudget,backgroundSecondConnectionBudget,
      secondConnectionBudget,backgroundConnectionDerivativeBudget,metricDensityBudget]
    positivity
  obtain ⟨F0,hF0⟩ := exists_flatCoefficientMatrix 2
  obtain ⟨ηE,hηE,hE⟩ := uniform_enlarged_framed_normal_elliptic
    (Y:=Y) hΩ (by omega) K ρ c₀ M Cj hK hρ 3 (by norm_num)
  obtain ⟨η0,hη0,h0⟩ := uniform_framed_normal_coefficient_closeness
    (Y:=Y) hΩ (by omega) K ρ c₀ M Cj hK hρ 2 (by norm_num)
  obtain ⟨η1,hη1,h1⟩ := uniform_framed_normal_coefficient_derivative
    (Y:=Y) hΩ hm K ρ c₀ M Cj hK hρ 2 (by norm_num)
  refine ⟨min ηE (min η0 η1),N0+N1,F0,lt_min hηE (lt_min hη0 hη1),add_nonneg hN0 hN1,hF0,?_⟩
  intro floor hf ε hε hSmall d hd y hy
  have hSE := hSmall.trans (min_le_left _ _)
  have hS0 := hSmall.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hS1 := hSmall.trans ((min_le_right _ _).trans (min_le_right _ _))
  let H := framedNormalMetric d.g₁ d.frame d.expMap y (d.radius y)
  have hEll : Elliptic (Metric.closedBall (0:X) 3) (4*K^2) H :=
    hE floor hf ε hε hSE d hd y hy d.g₁ (by simp)
  have hKpos : 0 < K := zero_lt_one.trans_le hK
  have hKPpos : 0 < 4*K^2 := by positivity
  have hr := (hd.2.2.2.2.1.2 y hy).1
  obtain ⟨c,hc,hScalar⟩ := hd.1.normal_center_principal_scalar hd.2.1 hy (d.radius y)
  obtain ⟨F,hRep⟩ := hEll.exists_coefficient_representative hKPpos 2
  refine ⟨F,c,hc,hRep,?_,?_⟩
  · intro i j x hx
    have hGerm := coefficient_difference_germ F F0 c hRep hF0 hx i j
    rw [hGerm.eq_of_nhds]
    have hcEntry := congrArg (fun A : Mat => A i j) hScalar
    change principalCoefficient H 0 i j = c*(1:Mat) i j at hcEntry
    rw [← hcEntry]
    exact (h0 floor hf ε hε hS0 d hd y hy d.g₁ (by simp) x
      (unitBall_subset_closedBall_two hx) i j).trans
      (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right hN1) hr.le)
  · intro i j x hx
    have hGerm := coefficient_difference_germ F F0 c hRep hF0 hx i j
    rw [hGerm.fderiv_eq,fderiv_sub_const]
    exact (h1 floor hf ε hε hS1 d hd y hy d.g₁ (by simp) x
      (unitBall_subset_closedBall_two hx) i j).trans
      (mul_le_mul_of_nonneg_right (le_add_of_nonneg_left hN0) hr.le)

end ShrinkingSpheres
