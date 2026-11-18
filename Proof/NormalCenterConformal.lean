import Proof.UniformNormalCoefficientCloseness
import Proof.MetricRadiusScaling

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 600000
set_option maxSynthPendingDepth 15
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Matrix
open scoped ContDiff Matrix.Norms.Elementwise Gradient
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.EnergyBridge OAI.AnisotropicCalderon.ConnectionError
open OAI.AnisotropicCalderon.MetricOperator

lemma metricPair_scale_metric (g : MetricField) (a : ℝ) (y u v : X) :
    metricPair (fun x => a • g x) y u v = a*metricPair g y u v := by
  simp only [metricPair,Matrix.smul_apply,smul_eq_mul,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- Conformality makes the first-metric normal coefficient at the center
    a positive scalar multiple of the Euclidean metric in the admitted frame. -/
theorem Background.normal_center_conformal {Y Ω : Set X} {K : ℝ} {m : ℕ}
    {M : Fin (m+1) → ℝ} {γ g₁ g₂ : MetricField} {e : Frame}
    (hB : Background Ω K M γ g₁ g₂ e)
    {expMap : X × X → X} {R : X → ℝ}
    (hN : NormalCoordinates Y Ω γ expMap R) {y : X} (hy : y ∈ Y) (r : ℝ) :
    ∃ c : ℝ,0 < c ∧ framedNormalMetric g₁ e expMap y r 0 = c • (1:Mat) := by
  have hyΩ := hN.center_mem hy
  obtain ⟨a,ha,hMetric⟩ := hB.2.2.2.1 y hyΩ
  have hFrame := hB.2.2.2.2.2.2.2 y hyΩ
  refine ⟨a⁻¹,inv_pos.mpr ha,?_⟩
  ext i j
  rw [hN.framedNormalMetric_center hy g₁ e hFrame]
  have hPair : metricPair γ y (e y i) (e y j) = a*metricPair g₁ y (e y i) (e y j) := by
    calc
      metricPair γ y (e y i) (e y j) = metricPair (fun x => a • g₁ x) y (e y i) (e y j) := by
        simp only [metricPair,hMetric]
      _ = _ := metricPair_scale_metric g₁ a y (e y i) (e y j)
  rw [hFrame i j] at hPair
  change metricPair g₁ y (e y i) (e y j) = a⁻¹*(if i=j then 1 else 0)
  rw [hPair]
  field_simp

/-- In dimension three the divergence coefficient of c times the Euclidean
    metric is sqrt(c) times the identity. -/
lemma principalCoefficient_const_scalar (c : ℝ) (hc : 0 < c) (x : X) :
    principalCoefficient (fun _ => c • (1:Mat)) x = Real.sqrt c • (1:Mat) := by
  have hr : 0 < Real.sqrt c := Real.sqrt_pos.2 hc
  have hBase : principalCoefficient (fun _ : X => (1:Mat)) x = 1 := by
    simp [principalCoefficient,OAI.AnisotropicCalderon.vol]
  have hh := principalCoefficient_radius_sq (fun _ : X => (1:Mat)) (Real.sqrt c) hr x (by simp)
  simpa only [Real.sq_sqrt hc.le,hBase] using hh

/-- The center-metric harmonic equation is precisely the Euclidean flux equation
    up to a fixed positive scalar. -/
lemma coordinateFluxDivergence_const_scalar_metric (c : ℝ) (hc : 0 < c)
    (U : X → ℝ) (x : X) :
    coordinateFluxDivergence (metricDivergenceFlux (fun _ => c • (1:Mat)) U) x =
      Real.sqrt c*coordinateFluxDivergence (gradient U) x := by
  have hFlux : metricDivergenceFlux (fun _ => c • (1:Mat)) U =
      fun z => Real.sqrt c • gradient U z := by
    funext z
    change matrixOperatorMap (principalCoefficient (fun _ : X => c • (1:Mat)) z) (gradient U z) = _
    rw [principalCoefficient_const_scalar c hc z]
    ext i
    simp [matrixOperatorMap]
  rw [hFlux,coordinateFluxDivergence_const_smul]

end ShrinkingSpheres
