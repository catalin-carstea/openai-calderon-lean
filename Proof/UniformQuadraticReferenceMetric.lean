import Proof.NormalMetricSecondTaylor
import Proof.UniformNormalMetricCloseness

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option maxSynthPendingDepth 15
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set
namespace ShrinkingSpheres

def normalReferenceMetricClosenessBudget {m : ℕ} (hm : 2 ≤ m) (K : ℝ) (M : Fin (m+1) → ℝ) (L : ℝ) : ℝ :=
  normalReferenceMetricSecondBudget K (243*K*|M ⟨1,by omega⟩|)
    (backgroundConnectionDerivativeBudget hm K M) |M ⟨1,by omega⟩| |M ⟨2,by omega⟩| *K^4*(L+1)^2

/-- The actual reference normal metric differs from identity quadratically in
    radius, uniformly on every fixed enlarged ball and for every admitted profile. -/
theorem uniform_framed_reference_metric_quadratic {Y Ω : Set X} (hΩ : IsOpen Ω)
    {m : ℕ} (hm : 2 ≤ m) (K ρ c₀ : ℝ) (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ)
    (hK : 1 ≤ K) (hρ : 0 < ρ) (L : ℝ) (hL : 0 ≤ L) :
    ∃ η : ℝ,0 < η ∧ ∀ floor,1 ≤ floor → ∀ ε,0 ≤ ε → ε ≤ η → ∀ d,
      Admissible Y Ω K ρ c₀ M Cj floor ε d → ∀ y ∈ Y,
      ∀ z ∈ Metric.closedBall (0:X) L,∀ i j,
      |framedNormalMetric d.γ d.frame d.expMap y (d.radius y) z i j-(if i=j then 1 else 0)| ≤
        normalReferenceMetricClosenessBudget hm K M L*(d.radius y)^2 := by
  obtain ⟨η,hη,hControl⟩ := uniform_normal_control_on_disk (Y:=Y) hΩ hm K ρ c₀ M Cj hK hρ L hL
  refine ⟨η,hη,?_⟩
  intro floor hf ε hε hSmall d hd y hy z hz i j
  have hKpos : 0 < K := zero_lt_one.trans_le hK
  have hcenter := hd.2.1.center_mem hy
  have hframe := hd.1.2.2.2.2.2.2.2 y hcenter
  have hw : frameVector d.frame y z ∈ disk d.γ y L := frameVector_mem_disk d.γ d.frame y z L hframe hz
  have hPack := hControl floor hf ε hε hSmall d hd y hy (frameVector d.frame y z) hw
  let C := 243*K*|M ⟨1,by omega⟩|
  let D := backgroundConnectionDerivativeBudget hm K M
  let S := normalReferenceMetricSecondBudget K C D |M ⟨1,by omega⟩| |M ⟨2,by omega⟩|
  have hC : 0 ≤ C := by dsimp [C];positivity
  have hD : 0 ≤ D := by dsimp [D,backgroundConnectionDerivativeBudget];positivity
  have hS : 0 ≤ S := by
    dsimp [S,normalReferenceMetricSecondBudget,normalVelocitySecondErrorBudget,normalVariationErrorBudget];positivity
  have hMetric (x : X) (hx : x ∈ Ω) (a b : I) : ‖fderiv ℝ (fun z => d.γ z a b) x‖ ≤ |M ⟨1,by omega⟩| :=
    (hd.1.reference_fderiv_bound (by omega) hx a b).trans (le_abs_self _)
  have hMetric2 (x : X) (hx : x ∈ Ω) (a b : I) : ‖fderiv ℝ (fderiv ℝ (fun z => d.γ z a b)) x‖ ≤ |M ⟨2,by omega⟩| :=
    (hd.1.reference_second_fderiv_bound hm hx a b).trans (le_abs_self _)
  have hr := (hd.2.2.2.2.1.2 y hy).1
  have hv : ‖d.radius y • frameVector d.frame y z‖ ≤ d.radius y*(K*(L+1)) := by
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos hr]
    exact mul_le_mul_of_nonneg_left (hd.1.1.disk_norm_bound_radius hK hcenter hL hw) hr.le
  have hFrameNorm (a : I) : ‖d.frame y a‖ ≤ K := by
    have hwE : d.frame y a ∈ sphereAt d.γ y := by
      change metricPair d.γ y (d.frame y a) (d.frame y a) = 1
      simpa using hframe a a
    have hh := hd.1.1.sphere_norm_sq_bound hKpos hcenter hwE
    apply (sq_le_sq₀ (norm_nonneg _) hKpos.le).mp
    nlinarith only [hh,hK]
  have hb := hd.2.1.normalPullbackMetric_quadratic_bound hΩ hd.1.1 hKpos hC hD (abs_nonneg _) (abs_nonneg _)
    (fun x hx => hd.1.connection_budget hKpos (by omega) hx)
    (fun x hx => hd.1.connection_derivative_budget hΩ hKpos hm hx) hMetric hMetric2 hy
    (d.radius y • frameVector d.frame y z) (d.frame y i) (d.frame y j)
    hPack.1.1 hPack.1.2 (hPack.2.2.2.1.trans (by norm_num))
  have hb' : |framedNormalMetric d.γ d.frame d.expMap y (d.radius y) z i j-(if i=j then 1 else 0)| ≤
      S*‖d.radius y • frameVector d.frame y z‖^2*‖d.frame y i‖*‖d.frame y j‖ := by
    simpa only [framedNormalMetric,normalPullbackMetricPair,normalVerticalJacobian,
      ContinuousLinearMap.comp_apply,ContinuousLinearMap.inr_apply,hframe] using hb
  have hh : S*‖d.radius y • frameVector d.frame y z‖^2*‖d.frame y i‖*‖d.frame y j‖ ≤
      S*(d.radius y*(K*(L+1)))^2*K*K := by gcongr;exact hFrameNorm i;exact hFrameNorm j
  exact (hb'.trans hh).trans_eq (by dsimp only [S,C,D,normalReferenceMetricClosenessBudget];ring)

end ShrinkingSpheres
