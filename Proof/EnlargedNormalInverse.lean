import Proof.UniformNormalInverse

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxSynthPendingDepth 15
open Set
open scoped ContDiff
namespace ShrinkingSpheres

lemma Elliptic.disk_norm_sq_bound_radius {Ω : Set X} {K : ℝ} {g : MetricField}
    (hg : Elliptic Ω K g) (hK : 0 < K) {y : X} (hy : y ∈ Ω) {w : X} {L : ℝ} (hw : w ∈ disk g y L) :
    ‖w‖^2 ≤ K*L^2 := by
  have hl := (((hg.2 y hy).2 w).1).trans hw
  have hh := mul_le_mul_of_nonneg_left hl hK.le
  simpa only [← mul_assoc,mul_inv_cancel₀ hK.ne',one_mul] using hh

/-- Uniform normal Jacobian and inverse bounds on any fixed enlarged rescaled ball.
    The enlargement does not require an additional Dirichlet solvability premise. -/
theorem uniform_normal_control_on_disk {Y Ω : Set X} (hΩ : IsOpen Ω)
    {m : ℕ} (hm : 2 ≤ m) (K ρ c₀ : ℝ) (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ)
    (hK : 1 ≤ K) (hρ : 0 < ρ) (L : ℝ) (hL : 0 ≤ L) :
    ∃ η : ℝ,0 < η ∧ ∀ floor,1 ≤ floor → ∀ ε,0 ≤ ε → ε ≤ η → ∀ d,
      Admissible Y Ω K ρ c₀ M Cj floor ε d → ∀ y ∈ Y,∀ w ∈ disk d.γ y L,
      (d.radius y • w ∈ interior (disk d.γ y (max ρ (d.radius y))) ∧ ‖d.radius y • w‖ ≤ 1) ∧
      d.expMap (y,d.radius y • w) ∈ Ω ∧ ContDiffAt ℝ ∞ d.expMap (y,d.radius y • w) ∧
      ‖normalVerticalJacobian d.expMap y (d.radius y • w)-ContinuousLinearMap.id ℝ X‖ ≤ (1/2:ℝ) ∧
      ‖(normalVerticalJacobian d.expMap y (d.radius y • w)).inverse‖ ≤ 2 := by
  let C := 243*K*|M ⟨1,by omega⟩|
  let D := backgroundConnectionDerivativeBudget hm K M
  let B := normalVariationErrorBudget K C D
  let η := min (ρ/(2*(L+1))) (1/(2*(B+1)*(K+1)*(L+1)))
  have hKpos : 0 < K := zero_lt_one.trans_le hK
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hD : 0 ≤ D := by dsimp [D,backgroundConnectionDerivativeBudget]; positivity
  have hB : 0 ≤ B := by dsimp [B,normalVariationErrorBudget]; positivity
  have hDen : 0 < 2*(B+1)*(K+1)*(L+1) := by positivity
  refine ⟨η,lt_min (div_pos hρ (by positivity)) (one_div_pos.mpr hDen),?_⟩
  intro floor hf ε hε hSmall d hd y hy w hw
  have hεR : ε*(L+1) ≤ ρ/2 := by
    have hh := (le_div_iff₀ (show 0 < 2*(L+1) by positivity)).mp (hSmall.trans (min_le_left _ _))
    nlinarith only [hh]
  have hεD : ε*(2*(B+1)*(K+1)*(L+1)) ≤ 1 :=
    (le_div_iff₀ hDen).mp (hSmall.trans (min_le_right _ _))
  have hQK : K*(L+1) ≤ 2*(B+1)*(K+1)*(L+1) := by
    exact mul_le_mul_of_nonneg_right (show K ≤ 2*(B+1)*(K+1) by nlinarith [mul_nonneg hB hKpos.le]) (by positivity)
  have hQB : 2*B*K*(L+1) ≤ 2*(B+1)*(K+1)*(L+1) :=
    mul_le_mul_of_nonneg_right (show 2*B*K ≤ 2*(B+1)*(K+1) by nlinarith) (by positivity)
  have hεK : ε*(K*(L+1)) ≤ 1 := (mul_le_mul_of_nonneg_left hQK hε).trans hεD
  have hεBK : B*(ε*(K*(L+1))) ≤ (1/2:ℝ) := by
    have hh := (mul_le_mul_of_nonneg_left hQB hε).trans hεD
    nlinarith only [hh]
  have hr := (hd.2.2.2.2.1.2 y hy).1
  have hrad := (radius_bounds (d.radius y) (beta d.γ d.radius y) floor ε hr.le hf
    (hd.2.2.2.2.1.2 y hy).2.1 (hd.2.2.2.2.2 y hy).2).2.2
  have hwSq := hd.1.1.disk_norm_sq_bound_radius hKpos (hd.2.1.center_mem hy) hw
  have hwNorm : ‖w‖ ≤ K*(L+1) := by
    have hKsq : K ≤ K^2 := by nlinarith
    have hLsq : L^2 ≤ (L+1)^2 := by nlinarith
    have hh := mul_le_mul hKsq hLsq (sq_nonneg L) (sq_nonneg K)
    apply (sq_le_sq₀ (norm_nonneg w) (show 0 ≤ K*(L+1) by positivity)).mp
    nlinarith only [hwSq,hh]
  have hvNorm : ‖d.radius y • w‖ ≤ ε*(K*(L+1)) := by
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos hr]
    exact mul_le_mul hrad hwNorm (norm_nonneg w) hε
  have hv1 : ‖d.radius y • w‖ ≤ 1 := hvNorm.trans hεK
  have hNear : B*‖d.radius y • w‖ ≤ (1/2:ℝ) :=
    (mul_le_mul_of_nonneg_left hvNorm hB).trans hεBK
  have hrL : d.radius y*L < ρ := by
    have hh := mul_le_mul_of_nonneg_right hrad hL
    have hh' : ε*L ≤ ε*(L+1) := mul_le_mul_of_nonneg_left (by linarith : L ≤ L+1) hε
    exact (hh.trans hh').trans_lt (hεR.trans_lt (half_lt_self hρ))
  have hrMax : d.radius y*L < max ρ (d.radius y) := hrL.trans_le (le_max_left _ _)
  have hSq : (d.radius y*L)^2 < (max ρ (d.radius y))^2 :=
    (sq_lt_sq₀ (mul_nonneg hr.le hL) (hρ.le.trans (le_max_left _ _))).2 hrMax
  have hvInt : d.radius y • w ∈ interior (disk d.γ y (max ρ (d.radius y))) := by
    apply mem_interior_disk_of_metricPair_lt
    have hUpper : metricPair d.γ y w w ≤ L^2 := hw
    have hScaled : metricPair d.γ y (d.radius y • w) (d.radius y • w) ≤ (d.radius y*L)^2 := by
      rw [metricPair_smul_left,metricPair_smul_right]
      have hh := mul_le_mul_of_nonneg_left hUpper (sq_nonneg (d.radius y))
      nlinarith only [hh]
    exact hScaled.trans_lt hSq
  have hΓ0 : ∀ x ∈ Ω,‖connectionBilinear d.γ x‖ ≤ C := fun x hx => hd.1.connection_budget hKpos (by omega) hx
  have hΓ1 : ∀ x ∈ Ω,‖fderiv ℝ (connectionBilinear d.γ) x‖ ≤ D := fun x hx =>
    hd.1.connection_derivative_budget hΩ hKpos hm hx
  have hx := ((hd.2.1.2 y hy).2.2 (d.radius y • w) (interior_subset hvInt)).1
  obtain ⟨U,hU,hTube,hReg⟩ := hd.2.1.1
  have hExp : ContDiffAt ℝ ∞ d.expMap (y,d.radius y • w) :=
    hReg.contDiffAt (hU.mem_nhds (hTube ⟨hy,interior_subset hvInt⟩))
  exact ⟨⟨hvInt,hv1⟩,hx,hExp,(hd.2.1.normalVerticalJacobian_sub_id_bound hΩ hd.1.1 hKpos hC hD hΓ0 hΓ1 hy _ hvInt hv1).trans hNear,
    hd.2.1.normalVerticalJacobian_inverse_bound hΩ hd.1.1 hKpos hC hD hΓ0 hΓ1 hy _ hvInt hv1 hNear⟩

/-- The Jacobian and inverse portion of uniform normal control. -/
theorem uniform_normal_inverse_bound_on_disk {Y Ω : Set X} (hΩ : IsOpen Ω)
    {m : ℕ} (hm : 2 ≤ m) (K ρ c₀ : ℝ) (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ)
    (hK : 1 ≤ K) (hρ : 0 < ρ) (L : ℝ) (hL : 0 ≤ L) :
    ∃ η : ℝ,0 < η ∧ ∀ floor,1 ≤ floor → ∀ ε,0 ≤ ε → ε ≤ η → ∀ d,
      Admissible Y Ω K ρ c₀ M Cj floor ε d → ∀ y ∈ Y,∀ w ∈ disk d.γ y L,
      d.expMap (y,d.radius y • w) ∈ Ω ∧ ContDiffAt ℝ ∞ d.expMap (y,d.radius y • w) ∧
      ‖normalVerticalJacobian d.expMap y (d.radius y • w)-ContinuousLinearMap.id ℝ X‖ ≤ (1/2:ℝ) ∧
      ‖(normalVerticalJacobian d.expMap y (d.radius y • w)).inverse‖ ≤ 2 := by
  obtain ⟨η,hη,hControl⟩ := uniform_normal_control_on_disk hΩ hm K ρ c₀ M Cj hK hρ L hL
  exact ⟨η,hη,fun floor hf ε hε hSmall d hd y hy w hw =>
    (hControl floor hf ε hε hSmall d hd y hy w hw).2⟩



end ShrinkingSpheres
