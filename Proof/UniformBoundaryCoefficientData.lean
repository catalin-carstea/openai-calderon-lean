import Proof.UniformCenteredCoefficientData
import Proof.NegativeNormalInverse

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

/-- The actual normal and tangential coefficient operators have common inverse
    and radius-linear perturbation bounds, derived solely from the frozen geometry. -/
theorem uniform_actual_boundary_coefficient_data {Y Ω : Set X} (hΩ : IsOpen Ω)
    {m : ℕ} (hm : 3 ≤ m) (K ρ c₀ : ℝ) (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ)
    (hK : 1 ≤ K) (hρ : 0 < ρ) :
    ∃ η CI CN CT : ℝ,0 < η ∧ 0 ≤ CI ∧ 0 ≤ CN ∧ 0 ≤ CT ∧
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
        ‖(negativeBoundaryCoefficientMulL (normalCoefficientJet F)).inverse‖ ≤ CI ∧
        ‖negativeBoundaryCoefficientMulL (normalCoefficientJet F)-
          c • ContinuousLinearMap.id ℝ (OAI.AnisotropicCalderon.SphereHarmonic.SphereSobolev (-(1/2:ℝ)))‖ ≤ CN*d.radius y ∧
        ∀ j : I,‖negativeBoundaryCoefficientMulL (tangentCoefficientJet F j)‖ ≤ CT*d.radius y := by
  obtain ⟨ηG,Q,F0,hηG,hQ,hF0,hData⟩ :=
    uniform_actual_centered_flat_comparison (Y:=Y) hΩ hm K ρ c₀ M Cj hK hρ
  let KP := 4*K^2
  let lo := (metricDensityBudget KP)⁻¹*KP⁻¹
  let B := boundaryHalfMultiplierBudget
  let CN := B*36*Q
  let CT := B*78*Q
  have hKP : 0 < KP := by dsimp [KP];have := zero_lt_one.trans_le hK;positivity
  have hlo : 0 < lo := by dsimp [lo,metricDensityBudget];positivity
  have hB : 0 ≤ B := boundaryHalfMultiplierBudget_nonneg
  have hCN : 0 ≤ CN := by dsimp [CN];positivity
  have hCT : 0 ≤ CT := by dsimp [CT];positivity
  let δ := lo/(2*CN+1)
  have hδ : 0 < δ := div_pos hlo (by positivity)
  refine ⟨min ηG δ,2*lo⁻¹,CN,CT,lt_min hηG hδ,by positivity,hCN,hCT,?_⟩
  intro floor hf ε hε hSmall d hd y hy
  dsimp only
  obtain ⟨F,c,hcBounds,hc,hScalar,hRep,hUE,hValue,hDerivative⟩ :=
    hData floor hf ε hε (hSmall.trans (min_le_left _ _)) d hd y hy
  have hr := (hd.2.2.2.2.1.2 y hy).1
  have hrε := (radius_bounds (d.radius y) (beta d.γ d.radius y) floor ε hr.le hf
    (hd.2.2.2.2.1.2 y hy).2.1 (hd.2.2.2.2.2 y hy).2).2.2
  have hRecip : c⁻¹ ≤ lo⁻¹ := by simpa only [one_div] using one_div_le_one_div_of_le hlo hcBounds.1
  have hεlo : ε*(2*CN+1) ≤ lo :=
    (le_div_iff₀ (show 0 < 2*CN+1 by positivity)).mp (hSmall.trans (min_le_right _ _))
  have hCNr : CN*d.radius y ≤ lo/2 := by
    have h1 := mul_le_mul_of_nonneg_left hrε hCN
    nlinarith only [h1,hεlo,hε]
  have hHalf : c⁻¹*(B*(36*(Q*d.radius y))) ≤ (1/2:ℝ) := by
    have h0 : B*(36*(Q*d.radius y)) = CN*d.radius y := by dsimp [CN];ring
    rw [h0]
    have h1 := mul_le_mul_of_nonneg_left hCNr (inv_nonneg.mpr hc.le)
    have h2 := mul_le_mul_of_nonneg_right hRecip (show 0 ≤ lo/2 by positivity)
    have hEq : lo⁻¹*(lo/2) = (1/2:ℝ) := by field_simp
    exact h1.trans (h2.trans_eq hEq)
  have hInv := norm_negative_normal_inverse_le F F0 c (Q*d.radius y) _ _ hc
    (mul_nonneg hQ hr.le) hF0 hUE hValue hDerivative hHalf
  have hNormal := norm_negative_normal_error_le F F0 c (Q*d.radius y)
    (mul_nonneg hQ hr.le) hF0 hValue hDerivative
  refine ⟨F,c,hcBounds,hc,hScalar,hRep,hUE,hInv.trans ?_,hNormal.trans_eq ?_,?_⟩
  · exact mul_le_mul_of_nonneg_left hRecip (by norm_num)
  · dsimp [CN,B];ring
  · intro j
    exact (norm_negative_tangent_coefficient_le F F0 c (Q*d.radius y)
      (mul_nonneg hQ hr.le) hF0 hValue hDerivative j).trans_eq (by dsimp [CT,B];ring)

end ShrinkingSpheres
