import Proof.MetricCoefficientLipschitz
import Mathlib.Analysis.Calculus.MeanValue

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 600000
set_option maxSynthPendingDepth 15
open Set Filter
open scoped ContDiff Topology
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.EnergyBridge

/-- The pointwise coefficient Lipschitz estimate transfers a uniform metric
    first-derivative bound to the actual divergence coefficient. -/
theorem Elliptic.principalCoefficient_derivative_bound_of_convex {Ω : Set X}
    (hΩ : IsOpen Ω) (hConvex : Convex ℝ Ω) {K M : ℝ} {g : MetricField}
    (hg : Elliptic Ω K g) (hK : 0 < K) (hM : 0 ≤ M)
    (hD : ∀ x ∈ Ω,∀ i j,‖fderiv ℝ (fun z => g z i j) x‖ ≤ M)
    {y : X} (hy : y ∈ Ω) (i j : I) :
    ‖fderiv ℝ (fun z => principalCoefficient g z i j) y‖ ≤
      metricDensityBudget K*(9*K^2+18*K^3)*M := by
  apply norm_fderiv_le_of_lip' ℝ (by unfold metricDensityBudget; positivity)
  filter_upwards [hΩ.mem_nhds hy] with x hx
  have hDiff (a b : I) : |g x a b-g y a b| ≤ M*‖x-y‖ := by
    simpa only [Real.norm_eq_abs] using Convex.norm_image_sub_le_of_norm_fderiv_le
      (fun z hz => ((hg.1 a b).contDiffAt (hΩ.mem_nhds hz)).differentiableAt (by simp))
      (fun z hz => hD z hz a b) hConvex hy hx
  have hb := hg.principalCoefficient_difference_bound hg hK hx hy (M*‖x-y‖)
    (mul_nonneg hM (norm_nonneg _)) hDiff i j
  simpa only [Real.norm_eq_abs,mul_assoc] using hb

end ShrinkingSpheres
