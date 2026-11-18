import Proof.FirstMetricNormalDensity
import Proof.NormalCenterCoefficient

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set
open scoped Matrix.Norms.Elementwise
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.EnergyBridge

/-- The actual scalar normal center coefficient is the frozen positive
    first-metric density factor, for every radius and admitted frame. -/
theorem Admissible.firstMetric_normal_principal_center {Y Ω : Set X} {m : ℕ}
    {K ρ c₀ floor ε : ℝ} {M : Fin (m+1) → ℝ} {Cj : Fin 9 → ℝ} {d : Data}
    (hd : Admissible Y Ω K ρ c₀ M Cj floor ε d) (hK : 0 < K)
    {y : X} (hy : y ∈ Y) (r : ℝ) :
    principalCoefficient (framedNormalMetric d.g₁ d.frame d.expMap y r) 0 =
      firstMetricDensityFactor d.γ d.g₁ y • (1:Mat) := by
  have hFrame := hd.1.2.2.2.2.2.2.2 y (hd.2.1.center_mem hy)
  have hFirst : framedNormalMetric d.g₁ d.frame d.expMap y r 0 =
      (firstMetricDensityFactor d.γ d.g₁ y)^2 • (1:Mat) := by
    ext k l
    rw [hd.2.1.framedNormalMetric_center hy d.g₁ d.frame hFrame,
      hd.1.firstMetricPair_eq_conformalFactor hK (hd.2.1.center_mem hy),
      ← hd.1.firstMetricDensityFactor_sq hK (hd.2.1.center_mem hy),hFrame k l]
    rfl
  have hScale := principalCoefficient_radius_sq (fun _ : X => (1:Mat))
    (firstMetricDensityFactor d.γ d.g₁ y) (firstMetricDensityFactor_pos _ _ _) (0:X) (by simp)
  have hFlat : principalCoefficient (fun _ : X => (1:Mat)) (0:X) = 1 := by
    simp [principalCoefficient,OAI.AnisotropicCalderon.vol]
  rw [hFlat] at hScale
  simpa only [principalCoefficient,OAI.AnisotropicCalderon.vol,hFirst] using hScale

end ShrinkingSpheres
