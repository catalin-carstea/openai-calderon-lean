import Proof.UniformNormalMetricDerivative
import Proof.MetricCoefficientDerivative
import Proof.UniformNormalCoefficientCloseness

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxSynthPendingDepth 15
open Set
open scoped ContDiff
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.EnergyBridge

def normalCoefficientAngularDerivativeBudget {m : ℕ} (hm : 3 ≤ m) (K : ℝ) (M : Fin (m+1) → ℝ) : ℝ :=
  metricDensityBudget (4*K^2)*(9*(4*K^2)^2+18*(4*K^2)^3)*normalMetricAngularDerivativeBudget hm K M

/-- Uniform O(radius) first angular jets of the actual divergence coefficient,
    throughout every fixed enlarged rescaled ball. -/
theorem uniform_framed_normal_coefficient_derivative {Y Ω : Set X} (hΩ : IsOpen Ω)
    {m : ℕ} (hm : 3 ≤ m) (K ρ c₀ : ℝ) (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ)
    (hK : 1 ≤ K) (hρ : 0 < ρ) (L : ℝ) (hL : 0 ≤ L) :
    ∃ η : ℝ,0 < η ∧ ∀ floor,1 ≤ floor → ∀ ε,0 ≤ ε → ε ≤ η → ∀ d,
      Admissible Y Ω K ρ c₀ M Cj floor ε d → ∀ y ∈ Y,
      ∀ g ∈ ({d.γ,d.g₁} : Set MetricField),∀ z ∈ Metric.closedBall (0:X) L,∀ i j,
      ‖fderiv ℝ (fun w => principalCoefficient
        (framedNormalMetric g d.frame d.expMap y (d.radius y)) w i j) z‖ ≤
        normalCoefficientAngularDerivativeBudget hm K M*d.radius y := by
  obtain ⟨ηD,hηD,hD⟩ := uniform_framed_normal_metric_derivative
    (Y:=Y) hΩ hm K ρ c₀ M Cj hK hρ (L+1) (by positivity)
  obtain ⟨ηE,hηE,hE⟩ := uniform_enlarged_framed_normal_elliptic
    (Y:=Y) hΩ (by omega) K ρ c₀ M Cj hK hρ (L+1) (by positivity)
  refine ⟨min ηD ηE,lt_min hηD hηE,?_⟩
  intro floor hf ε hε hSmall d hd y hy g hmem z hz i j
  let H := framedNormalMetric g d.frame d.expMap y (d.radius y)
  have hEll : Elliptic (Metric.closedBall (0:X) (L+1)) (4*K^2) H :=
    hE floor hf ε hε (hSmall.trans (min_le_right _ _)) d hd y hy g hmem
  have hEllOpen : Elliptic (Metric.ball (0:X) (L+1)) (4*K^2) H :=
    ⟨fun a b => (hEll.1 a b).mono Metric.ball_subset_closedBall,
      fun x hx => hEll.2 x (Metric.ball_subset_closedBall hx)⟩
  have hKpos : 0 < K := zero_lt_one.trans_le hK
  have hGeom : 0 ≤ normalMetricAngularDerivativeBudget hm K M := by
    unfold normalMetricAngularDerivativeBudget backgroundSecondNormalVariationBudget secondNormalVariationBudget
      backgroundSecondConnectionBudget secondConnectionBudget backgroundConnectionDerivativeBudget
    positivity
  have hr := (hd.2.2.2.2.1.2 y hy).1
  have hzOpen : z ∈ Metric.ball (0:X) (L+1) := by
    change dist z 0 < L+1
    change dist z 0 ≤ L at hz
    linarith
  have hMetric (x : X) (hx : x ∈ Metric.ball (0:X) (L+1)) (a b : I) :
      ‖fderiv ℝ (fun w => H w a b) x‖ ≤ normalMetricAngularDerivativeBudget hm K M*d.radius y :=
    hD floor hf ε hε (hSmall.trans (min_le_left _ _)) d hd y hy g hmem x
      (Metric.ball_subset_closedBall hx) a b
  have hb := hEllOpen.principalCoefficient_derivative_bound_of_convex Metric.isOpen_ball
    (convex_ball (0:X) (L+1)) (by positivity) (mul_nonneg hGeom hr.le) hMetric hzOpen i j
  exact hb.trans_eq (by unfold normalCoefficientAngularDerivativeBudget; ring)

end ShrinkingSpheres
