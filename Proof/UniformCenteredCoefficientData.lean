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

/-- Uniform local C1 representatives retain the actual conformal center scalar,
    its common lower bound, and ellipticity for the radial conversion. -/
theorem uniform_actual_centered_flat_comparison {Y Ω : Set X} (hΩ : IsOpen Ω)
    {m : ℕ} (hm : 3 ≤ m) (K ρ c₀ : ℝ) (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ)
    (hK : 1 ≤ K) (hρ : 0 < ρ) :
    ∃ η Q : ℝ,∃ F0 : SmoothCoefficientMatrix 2,0 < η ∧ 0 ≤ Q ∧
      (∀ x ∈ Metric.closedBall (0:X) 2,coefficientMatrixField 2 F0 x = 1) ∧
      ∀ floor,1 ≤ floor → ∀ ε,0 ≤ ε → ε ≤ η → ∀ d,
      Admissible Y Ω K ρ c₀ M Cj floor ε d → ∀ y ∈ Y,
      let H := framedNormalMetric d.g₁ d.frame d.expMap y (d.radius y)
      let KP := 4*K^2
      let lo := (metricDensityBudget KP)⁻¹*KP⁻¹
      let hi := metricDensityBudget KP*KP
      ∃ F : SmoothCoefficientMatrix 2,∃ c : ℝ,c ∈ Icc lo hi ∧ 0 < c ∧
        principalCoefficient H 0 = c • (1:Mat) ∧
        (∀ x ∈ Metric.closedBall (0:X) 2,∀ i j,
          coefficientValue 2 (F i j) =ᶠ[𝓝 x] (fun z => principalCoefficient H z i j)) ∧
        TauCeti.PDE.UniformlyEllipticOn (ballOpens : Set X) (coefficientMatrixField 2 F) lo hi ∧
        (∀ i j,∀ x ∈ (ballOpens : Set X),|coefficientValue 2 ((F-c • F0) i j) x| ≤ Q*d.radius y) ∧
        (∀ i j,∀ x ∈ (ballOpens : Set X),‖fderiv ℝ (coefficientValue 2 ((F-c • F0) i j)) x‖ ≤ Q*d.radius y) := by
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
  dsimp only
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
  have hKP : 1 ≤ 4*K^2 := by nlinarith only [hK,sq_nonneg (K-1)]
  have hcBounds := hEll.scalar_principal_coefficient_bounds hKP (by simp) c hScalar
  obtain ⟨F,hRep⟩ := hEll.exists_coefficient_representative hKPpos 2
  have hBall3 : (ballOpens : Set X) ⊆ Metric.closedBall (0:X) 3 :=
    unitBall_subset_closedBall_two.trans (Metric.closedBall_subset_closedBall (by norm_num))
  have hUE0 := (hEll.principalCoefficient_tau hKP).mono_set hBall3
  have hUE : TauCeti.PDE.UniformlyEllipticOn (ballOpens : Set X) (coefficientMatrixField 2 F)
      ((metricDensityBudget (4*K^2))⁻¹*(4*K^2)⁻¹) (metricDensityBudget (4*K^2)*(4*K^2)) := by
    apply hUE0.congr
    intro x hx
    ext i j
    exact (hRep x (unitBall_subset_closedBall_two hx) i j).eq_of_nhds
  refine ⟨F,c,hcBounds,hc,hScalar,hRep,hUE,?_,?_⟩
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
