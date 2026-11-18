import Proof.UniformQuadraticReferenceDerivative
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

def normalReferenceCoefficientAngularDerivativeBudget {m : ℕ} (hm : 3 ≤ m) (K : ℝ) (M : Fin (m+1) → ℝ) (L : ℝ) : ℝ :=
  metricDensityBudget (4*K^2)*(9*(4*K^2)^2+18*(4*K^2)^3)*normalReferenceMetricAngularDerivativeBudget hm K M (L+1)

/-- Uniform quadratic first angular jets of the actual reference divergence
    coefficient throughout each fixed enlarged rescaled ball. -/
theorem uniform_framed_reference_coefficient_derivative_quadratic {Y Ω : Set X} (hΩ : IsOpen Ω)
    {m : ℕ} (hm : 3 ≤ m) (K ρ c₀ : ℝ) (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ)
    (hK : 1 ≤ K) (hρ : 0 < ρ) (L : ℝ) (hL : 0 ≤ L) :
    ∃ η : ℝ,0 < η ∧ ∀ floor,1 ≤ floor → ∀ ε,0 ≤ ε → ε ≤ η → ∀ d,
      Admissible Y Ω K ρ c₀ M Cj floor ε d → ∀ y ∈ Y,
      ∀ z ∈ Metric.closedBall (0:X) L,∀ i j,
      ‖fderiv ℝ (fun w => principalCoefficient
        (framedNormalMetric d.γ d.frame d.expMap y (d.radius y)) w i j) z‖ ≤
        normalReferenceCoefficientAngularDerivativeBudget hm K M L*(d.radius y)^2 := by
  obtain ⟨ηD,hηD,hD⟩ := uniform_framed_reference_metric_derivative_quadratic
    (Y:=Y) hΩ hm K ρ c₀ M Cj hK hρ (L+1) (by positivity)
  obtain ⟨ηE,hηE,hE⟩ := uniform_enlarged_framed_normal_elliptic
    (Y:=Y) hΩ (by omega) K ρ c₀ M Cj hK hρ (L+1) (by positivity)
  refine ⟨min ηD ηE,lt_min hηD hηE,?_⟩
  intro floor hf ε hε hSmall d hd y hy z hz i j
  let H := framedNormalMetric d.γ d.frame d.expMap y (d.radius y)
  have hEll : Elliptic (Metric.closedBall (0:X) (L+1)) (4*K^2) H :=
    hE floor hf ε hε (hSmall.trans (min_le_right _ _)) d hd y hy d.γ (by simp)
  have hEllOpen : Elliptic (Metric.ball (0:X) (L+1)) (4*K^2) H :=
    ⟨fun a b => (hEll.1 a b).mono Metric.ball_subset_closedBall,
      fun x hx => hEll.2 x (Metric.ball_subset_closedBall hx)⟩
  have hKpos : 0 < K := zero_lt_one.trans_le hK
  have hGeom : 0 ≤ normalReferenceMetricAngularDerivativeBudget hm K M (L+1) := by
    dsimp [normalReferenceMetricAngularDerivativeBudget,normalReferenceMetricDerivativeBudget,
      secondVelocityPrincipalErrorBudget,secondNormalVariationBudget,normalVariationErrorBudget,
      backgroundSecondConnectionBudget,secondConnectionBudget,backgroundConnectionDerivativeBudget]
    positivity
  have hr := (hd.2.2.2.2.1.2 y hy).1
  have hzOpen : z ∈ Metric.ball (0:X) (L+1) := by
    change dist z 0 < L+1
    change dist z 0 ≤ L at hz
    linarith
  have hMetric (x : X) (hx : x ∈ Metric.ball (0:X) (L+1)) (a b : I) :
      ‖fderiv ℝ (fun w => H w a b) x‖ ≤ normalReferenceMetricAngularDerivativeBudget hm K M (L+1)*(d.radius y)^2 :=
    hD floor hf ε hε (hSmall.trans (min_le_left _ _)) d hd y hy x
      (Metric.ball_subset_closedBall hx) a b
  have hb := hEllOpen.principalCoefficient_derivative_bound_of_convex Metric.isOpen_ball
    (convex_ball (0:X) (L+1)) (by positivity) (mul_nonneg hGeom (sq_nonneg _)) hMetric hzOpen i j
  exact hb.trans_eq (by unfold normalReferenceCoefficientAngularDerivativeBudget; ring)

end ShrinkingSpheres
