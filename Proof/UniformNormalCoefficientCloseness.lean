import Proof.UniformNormalMetricCloseness
import Proof.MetricCoefficientLipschitz

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option maxSynthPendingDepth 15
open Set
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.EnergyBridge

lemma NormalCoordinates.framedNormalMetric_center {Y Ω : Set X} {γ : MetricField}
    {expMap : X × X → X} {R : X → ℝ}
    (hN : NormalCoordinates Y Ω γ expMap R) {y : X} (hy : y ∈ Y) (g : MetricField) (e : Frame)
    (hframe : ∀ i j,metricPair γ y (e y i) (e y j) = if i = j then 1 else 0)
    (r : ℝ) (i j : I) :
    framedNormalMetric g e expMap y r 0 i j = metricPair g y (e y i) (e y j) := by
  have hZero : frameVector e y (0:X) = 0 := by simp [frameVector]
  simp only [framedNormalMetric,normalPullbackMetricPair,hZero,smul_zero,hN.exp_zero hy,hN.vertical_zero hy e hframe]

def normalPrincipalClosenessBudget {m : ℕ} (hm : 2 ≤ m) (K : ℝ) (M : Fin (m+1) → ℝ) (L : ℝ) : ℝ :=
  metricDensityBudget (4*K^2)*(9*(4*K^2)^2+18*(4*K^2)^3)*normalMetricClosenessBudget hm K M L

/-- Uniform radius-linear continuity of the actual rescaled divergence-form
    coefficient about its value at the center of the fixed ball. -/
theorem uniform_framed_normal_coefficient_closeness {Y Ω : Set X} (hΩ : IsOpen Ω)
    {m : ℕ} (hm : 2 ≤ m) (K ρ c₀ : ℝ) (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ)
    (hK : 1 ≤ K) (hρ : 0 < ρ) (L : ℝ) (hL : 0 ≤ L) :
    ∃ η : ℝ,0 < η ∧ ∀ floor,1 ≤ floor → ∀ ε,0 ≤ ε → ε ≤ η → ∀ d,
      Admissible Y Ω K ρ c₀ M Cj floor ε d → ∀ y ∈ Y,
      ∀ g ∈ ({d.γ,d.g₁} : Set MetricField),∀ z ∈ Metric.closedBall (0:X) L,∀ i j,
      let H := framedNormalMetric g d.frame d.expMap y (d.radius y)
      |principalCoefficient H z i j-principalCoefficient H 0 i j| ≤ normalPrincipalClosenessBudget hm K M L*d.radius y := by
  obtain ⟨ηE,hηE,hE⟩ := uniform_enlarged_framed_normal_elliptic hΩ hm K ρ c₀ M Cj hK hρ L hL
  obtain ⟨ηM,hηM,hClose⟩ := uniform_framed_normal_metric_closeness hΩ hm K ρ c₀ M Cj hK hρ L hL
  refine ⟨min ηE ηM,lt_min hηE hηM,?_⟩
  intro floor hf ε hε hSmall d hd y hy g hmem z hz i j
  let H := framedNormalMetric g d.frame d.expMap y (d.radius y)
  have hEll : Elliptic (Metric.closedBall (0:X) L) (4*K^2) H :=
    hE floor hf ε hε (hSmall.trans (min_le_left _ _)) d hd y hy g hmem
  have h0 : (0:X) ∈ Metric.closedBall (0:X) L := by simpa only [Metric.mem_closedBall,dist_self] using hL
  have hframe := hd.1.2.2.2.2.2.2.2 y (hd.2.1.center_mem hy)
  have hDiff (a b : I) : |H z a b-H 0 a b| ≤ normalMetricClosenessBudget hm K M L*d.radius y := by
    change |framedNormalMetric g d.frame d.expMap y (d.radius y) z a b-
      framedNormalMetric g d.frame d.expMap y (d.radius y) 0 a b| ≤ _
    rw [hd.2.1.framedNormalMetric_center hy g d.frame hframe]
    exact hClose floor hf ε hε (hSmall.trans (min_le_right _ _)) d hd y hy g hmem z hz a b
  have hKpos : 0 < K := zero_lt_one.trans_le hK
  have hConst : 0 < 4*K^2 := by positivity
  have hGeom : 0 ≤ normalMetricClosenessBudget hm K M L := by
    unfold normalMetricClosenessBudget normalVariationErrorBudget backgroundConnectionDerivativeBudget
    positivity
  have hr := (hd.2.2.2.2.1.2 y hy).1
  have hb := hEll.principalCoefficient_difference_bound hEll hConst hz h0
    (normalMetricClosenessBudget hm K M L*d.radius y) (mul_nonneg hGeom hr.le) hDiff i j
  exact hb.trans_eq (by unfold normalPrincipalClosenessBudget; ring)

end ShrinkingSpheres
