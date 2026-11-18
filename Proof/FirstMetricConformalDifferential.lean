import Proof.FirstMetricConformalDepth
import Proof.MetricKoszul
import Proof.NormalMetricDerivative

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1300000
set_option maxSynthPendingDepth 15
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter
open scoped ContDiff Topology
namespace ShrinkingSpheres

/-- Exact first metric differential in terms of the canonical conformal depth. -/
theorem Background.firstMetric_metricDifferential {Ω : Set X} (hΩ : IsOpen Ω)
    {K : ℝ} {m : ℕ} {M : Fin (m+1) → ℝ} {γ g₁ g₂ : MetricField} {e : Frame}
    (hB : Background Ω K M γ g₁ g₂ e) (hK : 0 < K) {x : X} (hx : x ∈ Ω) (a b c : X) :
    metricDifferential g₁ x a b c = Real.exp (-2*firstMetricConformalDepth γ g₁ x)*
      (metricDifferential γ x a b c-2*fderiv ℝ (firstMetricConformalDepth γ g₁) x a*metricPair γ x b c) := by
  let t := firstMetricConformalDepth γ g₁
  let A := fun y => Real.exp (-2*t y)
  let F := fun y => metricPair γ y b c
  have ht := (((hB.firstMetricConformalDepth_smooth hK).contDiffAt (hΩ.mem_nhds hx)).differentiableAt (by simp)).hasFDerivAt
  have hA := (ht.const_smul (-2:ℝ)).exp
  have hF : DifferentiableAt ℝ F x := metric_pair_comp_differentiableAt hΩ hB.1
    (fun y => y) (fun _ => b) (fun _ => c) x hx differentiableAt_id (differentiableAt_const _) (differentiableAt_const _)
  have hProduct := hA.mul hF.hasFDerivAt
  have hEq : (fun y => metricPair g₁ y b c) =ᶠ[𝓝 x] (fun y => A y*F y) := by
    filter_upwards [hΩ.mem_nhds hx] with y hy
    exact (hB.firstMetricPair_eq_conformalFactor hK hy b c).trans
      (congrArg (fun k => k*metricPair γ y b c) (hB.firstMetricConformalFactor_eq_exp_depth hK hy))
  have hD := congrArg (fun L : X →L[ℝ] ℝ => L a) (hEq.fderiv_eq.trans hProduct.fderiv)
  rw [fderiv_metricPair_fixed hΩ hB.2.1 hx a b c] at hD
  have hDF : fderiv ℝ F x a = metricDifferential γ x a b c := fderiv_metricPair_fixed hΩ hB.1 hx a b c
  simp only [ContinuousLinearMap.add_apply,ContinuousLinearMap.smul_apply,smul_smul,smul_eq_mul] at hD
  rw [hDF] at hD
  change metricDifferential g₁ x a b c = _ at hD
  exact hD.trans (by dsimp [A,t,F];ring)

end ShrinkingSpheres
