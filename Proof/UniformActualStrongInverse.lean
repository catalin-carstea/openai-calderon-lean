import Proof.UniformStrongC1Neighborhood
import Proof.UniformNormalCoefficientDerivative
import Proof.NormalCenterCoefficient
import Proof.PullbackCoefficientRepresentative

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option maxSynthPendingDepth 15
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter MeasureTheory
open scoped ContDiff Topology ENNReal Matrix.Norms.Elementwise
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.EnergyBridge OAI.AnisotropicCalderon.DirichletFamily

/-- A common H2-to-L2 strong Dirichlet inverse bound for the genuine first-metric
    normal coefficients. The compact representative retains the actual coefficient
    as a smooth germ on the regularity neighborhood. Only local C0/C1 smallness is used. -/
theorem uniform_actual_strong_dirichlet_inverse {Y Ω : Set X} (hΩ : IsOpen Ω)
    {m : ℕ} (hm : 3 ≤ m) (K ρ c₀ : ℝ) (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ)
    (hK : 1 ≤ K) (hρ : 0 < ρ) :
    ∃ η C : ℝ,0 < η ∧ 0 ≤ C ∧ ∀ floor,1 ≤ floor → ∀ ε,0 ≤ ε → ε ≤ η → ∀ d,
      Admissible Y Ω K ρ c₀ M Cj floor ε d → ∀ y ∈ Y,
      ∃ F : SmoothCoefficientMatrix 2,
        (∀ x ∈ Metric.closedBall (0:X) 2,∀ i j,
          coefficientValue 2 (F i j) =ᶠ[𝓝 x] (fun z => principalCoefficient
            (framedNormalMetric d.g₁ d.frame d.expMap y (d.radius y)) z i j)) ∧
        ‖(strongDirichletOperator fixedSobolevCalculus 0 F).inverse‖ ≤ C := by
  let KP := 4*K^2
  let lo := (metricDensityBudget KP)⁻¹*KP⁻¹
  let hi := metricDensityBudget KP*KP
  let N0 := normalPrincipalClosenessBudget (by omega) K M 2
  let N1 := normalCoefficientAngularDerivativeBudget hm K M
  let Q := N0+N1
  have hKpos : 0 < K := zero_lt_one.trans_le hK
  have hKP : 1 ≤ KP := by dsimp [KP]; nlinarith only [hK,sq_nonneg (K-1)]
  have hKPpos : 0 < KP := zero_lt_one.trans_le hKP
  have hlo : 0 < lo := by dsimp [lo,metricDensityBudget]; positivity
  have hN0 : 0 ≤ N0 := by
    dsimp [N0,normalPrincipalClosenessBudget,normalMetricClosenessBudget,normalVariationErrorBudget,
      backgroundConnectionDerivativeBudget,metricDensityBudget]
    positivity
  have hN1 : 0 ≤ N1 := by
    dsimp [N1,normalCoefficientAngularDerivativeBudget,normalMetricAngularDerivativeBudget,
      backgroundSecondNormalVariationBudget,secondNormalVariationBudget,backgroundSecondConnectionBudget,
      secondConnectionBudget,backgroundConnectionDerivativeBudget,metricDensityBudget]
    positivity
  have hQ : 0 ≤ Q := add_nonneg hN0 hN1
  obtain ⟨F0,hF0,δ,C,hδ,hC,hBound⟩ := exists_uniform_strongC1_neighborhood lo hi hlo
  obtain ⟨ηE,hηE,hE⟩ := uniform_enlarged_framed_normal_elliptic
    (Y:=Y) hΩ (by omega) K ρ c₀ M Cj hK hρ 3 (by norm_num)
  obtain ⟨η0,hη0,h0⟩ := uniform_framed_normal_coefficient_closeness
    (Y:=Y) hΩ (by omega) K ρ c₀ M Cj hK hρ 2 (by norm_num)
  obtain ⟨η1,hη1,h1⟩ := uniform_framed_normal_coefficient_derivative
    (Y:=Y) hΩ hm K ρ c₀ M Cj hK hρ 2 (by norm_num)
  let ηG := min ηE (min η0 η1)
  refine ⟨min ηG (δ/(Q+1)),C,lt_min (lt_min hηE (lt_min hη0 hη1))
    (div_pos hδ (by positivity)),hC,?_⟩
  intro floor hf ε hε hSmall d hd y hy
  have hSG : ε ≤ ηG := hSmall.trans (min_le_left _ _)
  have hSE := hSG.trans (min_le_left _ _)
  have hS0 := hSG.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hS1 := hSG.trans ((min_le_right _ _).trans (min_le_right _ _))
  let H := framedNormalMetric d.g₁ d.frame d.expMap y (d.radius y)
  have hEll : Elliptic (Metric.closedBall (0:X) 3) KP H :=
    hE floor hf ε hε hSE d hd y hy d.g₁ (by simp)
  have hr := (hd.2.2.2.2.1.2 y hy).1
  have hrε := (radius_bounds (d.radius y) (beta d.γ d.radius y) floor ε hr.le hf
    (hd.2.2.2.2.1.2 y hy).2.1 (hd.2.2.2.2.2 y hy).2).2.2
  have hSmallδ : ε*(Q+1) ≤ δ :=
    (le_div_iff₀ (show 0 < Q+1 by positivity)).mp (hSmall.trans (min_le_right _ _))
  have hQR : Q*d.radius y ≤ δ := by
    have hh := mul_le_mul_of_nonneg_left hrε hQ
    have hh' : Q*ε ≤ (Q+1)*ε := mul_le_mul_of_nonneg_right (by linarith) hε
    nlinarith only [hh,hh',hSmallδ]
  obtain ⟨c,hc,hScalar⟩ := hd.1.normal_center_principal_scalar hd.2.1 hy (d.radius y)
  have hcBounds : c ∈ Icc lo hi := hEll.scalar_principal_coefficient_bounds hKP (by simp) c hScalar
  obtain ⟨F,hRep⟩ := hEll.exists_coefficient_representative hKPpos 2
  have hBall3 : (ballOpens : Set X) ⊆ Metric.closedBall (0:X) 3 :=
    unitBall_subset_closedBall_two.trans (Metric.closedBall_subset_closedBall (by norm_num))
  have hUE0 := (hEll.principalCoefficient_tau hKP).mono_set hBall3
  have hUE : TauCeti.PDE.UniformlyEllipticOn (ballOpens : Set X) (coefficientMatrixField 2 F) lo hi := by
    apply hUE0.congr
    intro x hx
    ext i j
    exact (hRep x (unitBall_subset_closedBall_two hx) i j).eq_of_nhds
  have hN0Q : N0 ≤ Q := le_add_of_nonneg_right hN1
  have hN1Q : N1 ≤ Q := le_add_of_nonneg_left hN0
  have hVal (i j : I) (x : X) (hx : x ∈ (ballOpens : Set X)) :
      |coefficientValue 2 ((F-c • F0) i j) x| ≤ δ := by
    have hGerm := coefficient_difference_germ F F0 c hRep hF0 hx i j
    rw [hGerm.eq_of_nhds]
    have hcEntry := congrArg (fun A : Mat => A i j) hScalar
    change principalCoefficient H 0 i j = c*(1:Mat) i j at hcEntry
    rw [← hcEntry]
    have hb := h0 floor hf ε hε hS0 d hd y hy d.g₁ (by simp) x
      (unitBall_subset_closedBall_two hx) i j
    exact hb.trans ((mul_le_mul_of_nonneg_right hN0Q hr.le).trans hQR)
  have hDeriv (i j : I) (x : X) (hx : x ∈ (ballOpens : Set X)) :
      ‖fderiv ℝ (coefficientValue 2 ((F-c • F0) i j)) x‖ ≤ δ := by
    have hGerm := coefficient_difference_germ F F0 c hRep hF0 hx i j
    rw [hGerm.fderiv_eq,fderiv_sub_const]
    have hb := h1 floor hf ε hε hS1 d hd y hy d.g₁ (by simp) x
      (unitBall_subset_closedBall_two hx) i j
    exact hb.trans ((mul_le_mul_of_nonneg_right hN1Q hr.le).trans hQR)
  exact ⟨F,hRep,hBound c hcBounds F lo hi hUE hVal hDeriv⟩

end ShrinkingSpheres
