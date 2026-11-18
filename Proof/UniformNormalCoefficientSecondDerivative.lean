import Proof.UniformNormalMetricSecondDerivative
import Proof.UniformNormalCoefficientDerivative
import Proof.MetricCoefficientSecondDerivative

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1400000
set_option maxSynthPendingDepth 20
open Set
open scoped ContDiff
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.EnergyBridge

def normalCoefficientAngularSecondDerivativeBudget {m : ℕ} (hm : 4 ≤ m) (K : ℝ) (M : Fin (m+1) → ℝ) : ℝ :=
  let K' := 4*K^2
  let A := |normalMetricAngularDerivativeBudget (show 3 ≤ m by omega) K M|
  let B := |normalMetricAngularSecondDerivativeBudget hm K M|
  metricDensityBudget K'*(K'*(9*(972*K'^2*A^2+27*K'*B))+
    2*(81*K'*A)*(9*K'^2*A)+9*(162*K'^3*A^2+9*K'^2*B))

/-- Genuine second angular jets of the normalized divergence coefficient are
    uniformly quadratic in the radius, on every fixed enlarged ball. -/
theorem uniform_framed_normal_coefficient_second_derivative {Y Ω : Set X} (hY : IsOpen Y) (hΩ : IsOpen Ω)
    {m : ℕ} (hm : 4 ≤ m) (K ρ c₀ : ℝ) (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ)
    (hK : 1 ≤ K) (hρ : 0 < ρ) (L : ℝ) (hL : 0 ≤ L) :
    ∃ η : ℝ,0 < η ∧ ∀ floor,1 ≤ floor → ∀ ε,0 ≤ ε → ε ≤ η → ∀ d,
      Admissible Y Ω K ρ c₀ M Cj floor ε d → ∀ y ∈ Y,
      ∀ g ∈ ({d.γ,d.g₁} : Set MetricField),∀ z ∈ Metric.closedBall (0:X) L,∀ i j,
      ‖fderiv ℝ (fderiv ℝ (fun w => principalCoefficient
        (framedNormalMetric g d.frame d.expMap y (d.radius y)) w i j)) z‖ ≤
        normalCoefficientAngularSecondDerivativeBudget hm K M*(d.radius y)^2 := by
  obtain ⟨η1,hη1,hD1⟩ := uniform_framed_normal_metric_derivative
    (Y:=Y) hΩ (by omega) K ρ c₀ M Cj hK hρ (L+1) (by positivity)
  obtain ⟨η2,hη2,hD2⟩ := uniform_framed_normal_metric_second_derivative
    hY hΩ hm K ρ c₀ M Cj hK hρ (L+1) (by positivity)
  obtain ⟨ηE,hηE,hE⟩ := uniform_enlarged_framed_normal_elliptic
    (Y:=Y) hΩ (by omega) K ρ c₀ M Cj hK hρ (L+1) (by positivity)
  refine ⟨min η1 (min η2 ηE),lt_min hη1 (lt_min hη2 hηE),?_⟩
  intro floor hf ε hε hSmall d hd y hy g hmem z hz i j
  let H := framedNormalMetric g d.frame d.expMap y (d.radius y)
  let A := |normalMetricAngularDerivativeBudget (show 3 ≤ m by omega) K M|
  let B := |normalMetricAngularSecondDerivativeBudget hm K M|
  have hEll : Elliptic (Metric.closedBall (0:X) (L+1)) (4*K^2) H :=
    hE floor hf ε hε (hSmall.trans ((min_le_right _ _).trans (min_le_right _ _))) d hd y hy g hmem
  have hEllOpen : Elliptic (Metric.ball (0:X) (L+1)) (4*K^2) H :=
    ⟨fun a b => (hEll.1 a b).mono Metric.ball_subset_closedBall,
      fun x hx => hEll.2 x (Metric.ball_subset_closedBall hx)⟩
  have hKpos : 0 < K := zero_lt_one.trans_le hK
  have hr := (hd.2.2.2.2.1.2 y hy).1
  have hzOpen : z ∈ Metric.ball (0:X) (L+1) := by
    change dist z 0 < L+1
    change dist z 0 ≤ L at hz
    linarith
  have hMetric1 (a b : I) : ‖fderiv ℝ (fun w => H w a b) z‖ ≤ A*d.radius y := by
    exact (hD1 floor hf ε hε (hSmall.trans (min_le_left _ _)) d hd y hy g hmem z
      (Metric.closedBall_subset_closedBall (by linarith) hz) a b).trans
      (mul_le_mul_of_nonneg_right (le_abs_self _) hr.le)
  have hMetric2 (a b : I) : ‖fderiv ℝ (fderiv ℝ (fun w => H w a b)) z‖ ≤ B*(d.radius y)^2 := by
    exact (hD2 floor hf ε hε (hSmall.trans ((min_le_right _ _).trans (min_le_left _ _))) d hd y hy g hmem z
      (Metric.closedBall_subset_closedBall (by linarith) hz) a b).trans
      (mul_le_mul_of_nonneg_right (le_abs_self _) (sq_nonneg _))
  have hb := hEllOpen.principalCoefficient_second_fderiv_bound Metric.isOpen_ball (by positivity) hzOpen
    (A*d.radius y) (B*(d.radius y)^2) (by dsimp [A];positivity) (by dsimp [B];positivity) hMetric1 hMetric2 i j
  exact hb.trans_eq (by dsimp only [normalCoefficientAngularSecondDerivativeBudget,A,B];ring)

end ShrinkingSpheres
