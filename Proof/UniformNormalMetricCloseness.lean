import Proof.NormalMetricCloseness

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option maxSynthPendingDepth 15
open Set
namespace ShrinkingSpheres

def normalMetricClosenessBudget {m : ℕ} (hm : 2 ≤ m) (K : ℝ) (M : Fin (m+1) → ℝ) (L : ℝ) : ℝ :=
  (36*|M ⟨1,by omega⟩| *K+3*K*normalVariationErrorBudget K
    (243*K*|M ⟨1,by omega⟩|) (backgroundConnectionDerivativeBudget hm K M))*K^3*(L+1)

lemma Elliptic.disk_norm_bound_radius {Ω : Set X} {K : ℝ} {g : MetricField}
    (hg : Elliptic Ω K g) (hK : 1 ≤ K) {y : X} (hy : y ∈ Ω) {w : X}
    {L : ℝ} (hL : 0 ≤ L) (hw : w ∈ disk g y L) : ‖w‖ ≤ K*(L+1) := by
  have hs := hg.disk_norm_sq_bound_radius (zero_lt_one.trans_le hK) hy hw
  have hKsq : K ≤ K^2 := by nlinarith
  have hLsq : L^2 ≤ (L+1)^2 := by nlinarith
  have hh := mul_le_mul hKsq hLsq (sq_nonneg L) (sq_nonneg K)
  apply (sq_le_sq₀ (norm_nonneg w) (show 0 ≤ K*(L+1) by positivity)).mp
  nlinarith only [hs,hh]

/-- A uniform radius-linear estimate for the actual framed pullback metric,
    throughout a fixed enlarged closed ball and for every admitted profile. -/
theorem uniform_framed_normal_metric_closeness {Y Ω : Set X} (hΩ : IsOpen Ω)
    {m : ℕ} (hm : 2 ≤ m) (K ρ c₀ : ℝ) (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ)
    (hK : 1 ≤ K) (hρ : 0 < ρ) (L : ℝ) (hL : 0 ≤ L) :
    ∃ η : ℝ,0 < η ∧ ∀ floor,1 ≤ floor → ∀ ε,0 ≤ ε → ε ≤ η → ∀ d,
      Admissible Y Ω K ρ c₀ M Cj floor ε d → ∀ y ∈ Y,
      ∀ g ∈ ({d.γ,d.g₁} : Set MetricField),∀ z ∈ Metric.closedBall (0:X) L,∀ i j,
      |framedNormalMetric g d.frame d.expMap y (d.radius y) z i j-
        metricPair g y (d.frame y i) (d.frame y j)| ≤ normalMetricClosenessBudget hm K M L*d.radius y := by
  obtain ⟨η,hη,hControl⟩ := uniform_normal_control_on_disk hΩ hm K ρ c₀ M Cj hK hρ L hL
  refine ⟨η,hη,?_⟩
  intro floor hf ε hε hSmall d hd y hy g hmem z hz i j
  have hKpos : 0 < K := zero_lt_one.trans_le hK
  have hcenter := hd.2.1.center_mem hy
  have hframe := hd.1.2.2.2.2.2.2.2 y hcenter
  have hEll : Elliptic Ω K g := by
    simp only [mem_insert_iff,mem_singleton_iff] at hmem
    rcases hmem with rfl | rfl
    · exact hd.1.1
    · exact hd.1.2.1
  have hw : frameVector d.frame y z ∈ disk d.γ y L :=
    frameVector_mem_disk d.γ d.frame y z L hframe hz
  have hPack := hControl floor hf ε hε hSmall d hd y hy (frameVector d.frame y z) hw
  let C := 243*K*|M ⟨1,by omega⟩|
  let D := backgroundConnectionDerivativeBudget hm K M
  let B := normalVariationErrorBudget K C D
  let S := 36*|M ⟨1,by omega⟩| *K+3*K*B
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hD : 0 ≤ D := by dsimp [D,backgroundConnectionDerivativeBudget]; positivity
  have hB : 0 ≤ B := by dsimp [B,normalVariationErrorBudget]; positivity
  have hS : 0 ≤ S := by dsimp [S]; positivity
  have hMetric : ∀ x ∈ Ω,∀ a b,‖fderiv ℝ (fun z => g z a b) x‖ ≤ |M ⟨1,by omega⟩| := by
    intro x hx a b
    have hh := hd.1.2.2.2.2.1 g hmem ⟨1,by omega⟩ a b x hx
    rw [norm_iteratedFDeriv_one] at hh
    exact hh.trans (le_abs_self _)
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
  have hb := hd.2.1.normalPullbackMetric_close hΩ hd.1.1 hEll hKpos hC hD (abs_nonneg _)
    (fun x hx => hd.1.connection_budget hKpos (by omega) hx)
    (fun x hx => hd.1.connection_derivative_budget hΩ hKpos hm hx)
    hMetric hy (d.radius y • frameVector d.frame y z) (d.frame y i) (d.frame y j)
    hPack.1.1 hPack.1.2 (hPack.2.2.2.1.trans (by norm_num))
  have hb' : |framedNormalMetric g d.frame d.expMap y (d.radius y) z i j-
      metricPair g y (d.frame y i) (d.frame y j)| ≤
      S*‖d.radius y • frameVector d.frame y z‖*‖d.frame y i‖*‖d.frame y j‖ := by
    simpa only [framedNormalMetric,normalPullbackMetricPair,normalVerticalJacobian,
      ContinuousLinearMap.comp_apply,ContinuousLinearMap.inr_apply] using hb
  have hh : S*‖d.radius y • frameVector d.frame y z‖*‖d.frame y i‖*‖d.frame y j‖ ≤
      S*(d.radius y*(K*(L+1)))*K*K := by gcongr; exact hFrameNorm i; exact hFrameNorm j
  exact (hb'.trans hh).trans_eq (by dsimp only [S,B,C,D,normalMetricClosenessBudget]; ring)

end ShrinkingSpheres
