import Proof.NormalJacobianInverse
import Proof.Smallness

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxSynthPendingDepth 15
open Set
namespace ShrinkingSpheres

lemma mem_interior_disk_of_metricPair_lt (g : MetricField) (y v : X) (R : ℝ)
    (hv : metricPair g y v v < R^2) : v ∈ interior (disk g y R) := by
  have hc : Continuous (fun z : X => metricPair g y z z) := by
    have hh := ((continuous_const : Continuous (fun _ : X => metricBilinear g y)).clm_apply continuous_id).clm_apply continuous_id
    simpa only [metricBilinear_apply,Function.id_def] using hh
  apply mem_interior_iff_mem_nhds.mpr
  have hNear : ∀ᶠ z in nhds v,metricPair g y z z < R^2 :=
    hc.continuousAt.eventually (isOpen_Iio.mem_nhds hv)
  exact Filter.mem_of_superset hNear (fun z hz => by
    change metricPair g y z z ≤ R^2
    exact hz.le)

lemma Elliptic.disk_norm_sq_bound {Ω : Set X} {K : ℝ} {g : MetricField}
    (hg : Elliptic Ω K g) (hK : 0 < K) {y : X} (hy : y ∈ Ω) {w : X} (hw : w ∈ disk g y 1) :
    ‖w‖^2 ≤ K := by
  have hUpper : metricPair g y w w ≤ 1 := by simpa only [disk,one_pow,mem_setOf_eq] using hw
  have hl := (((hg.2 y hy).2 w).1).trans hUpper
  have hh := mul_le_mul_of_nonneg_left hl hK.le
  simpa only [← mul_assoc,mul_inv_cancel₀ hK.ne',one_mul,mul_one] using hh

/-- A common positive smallness threshold makes the actual endpoint Jacobian close
    to the identity and uniformly invertible on every admissible closed rescaled normal ball.
    The threshold depends only on rho, ellipticity and the first two metric budgets. -/
theorem uniform_normal_inverse_bound {Y Ω : Set X} (hΩ : IsOpen Ω)
    {m : ℕ} (hm : 2 ≤ m) (K ρ c₀ : ℝ) (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ)
    (hK : 1 ≤ K) (hρ : 0 < ρ) :
    ∃ η : ℝ,0 < η ∧ ∀ floor,1 ≤ floor → ∀ ε,0 ≤ ε → ε ≤ η → ∀ d,
      Admissible Y Ω K ρ c₀ M Cj floor ε d → ∀ y ∈ Y,∀ w ∈ disk d.γ y 1,
      ‖normalVerticalJacobian d.expMap y (d.radius y • w)-ContinuousLinearMap.id ℝ X‖ ≤ (1/2:ℝ) ∧
      ‖(normalVerticalJacobian d.expMap y (d.radius y • w)).inverse‖ ≤ 2 := by
  let C := 243*K*|M ⟨1,by omega⟩|
  let D := backgroundConnectionDerivativeBudget hm K M
  let B := normalVariationErrorBudget K C D
  let η := min (ρ/2) (1/(2*(B+1)*(K+1)))
  have hKpos : 0 < K := zero_lt_one.trans_le hK
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hD : 0 ≤ D := by dsimp [D,backgroundConnectionDerivativeBudget]; positivity
  have hB : 0 ≤ B := by dsimp [B,normalVariationErrorBudget]; positivity
  have hDen : 0 < 2*(B+1)*(K+1) := by positivity
  refine ⟨η,lt_min (half_pos hρ) (one_div_pos.mpr hDen),?_⟩
  intro floor hf ε hε hSmall d hd y hy w hw
  have hεR : ε ≤ ρ/2 := hSmall.trans (min_le_left _ _)
  have hεD : ε*(2*(B+1)*(K+1)) ≤ 1 :=
    (le_div_iff₀ hDen).mp (hSmall.trans (min_le_right _ _))
  have hQK : K ≤ 2*(B+1)*(K+1) := by nlinarith [mul_nonneg hB hKpos.le]
  have hQB : 2*B*K ≤ 2*(B+1)*(K+1) := by nlinarith
  have hεK : ε*K ≤ 1 := (mul_le_mul_of_nonneg_left hQK hε).trans hεD
  have hεBK : B*(ε*K) ≤ (1/2:ℝ) := by
    have hh := (mul_le_mul_of_nonneg_left hQB hε).trans hεD
    nlinarith only [hh]
  have hr := (hd.2.2.2.2.1.2 y hy).1
  have hrad := (radius_bounds (d.radius y) (beta d.γ d.radius y) floor ε hr.le hf
    (hd.2.2.2.2.1.2 y hy).2.1 (hd.2.2.2.2.2 y hy).2).2.2
  have hwSq := hd.1.1.disk_norm_sq_bound hKpos (hd.2.1.center_mem hy) hw
  have hwNorm : ‖w‖ ≤ K := by nlinarith [norm_nonneg w]
  have hvNorm : ‖d.radius y • w‖ ≤ ε*K := by
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos hr]
    exact mul_le_mul hrad hwNorm (norm_nonneg w) hε
  have hv1 : ‖d.radius y • w‖ ≤ 1 := hvNorm.trans hεK
  have hNear : B*‖d.radius y • w‖ ≤ (1/2:ℝ) :=
    (mul_le_mul_of_nonneg_left hvNorm hB).trans hεBK
  have hrρ : d.radius y < ρ := hrad.trans_lt (hεR.trans_lt (half_lt_self hρ))
  have hrMax : d.radius y < max ρ (d.radius y) := hrρ.trans_le (le_max_left _ _)
  have hSq : (d.radius y)^2 < (max ρ (d.radius y))^2 :=
    (sq_lt_sq₀ hr.le (hr.le.trans (le_max_right _ _))).2 hrMax
  have hvInt : d.radius y • w ∈ interior (disk d.γ y (max ρ (d.radius y))) := by
    apply mem_interior_disk_of_metricPair_lt
    have hUpper : metricPair d.γ y w w ≤ 1 := by simpa only [disk,one_pow,mem_setOf_eq] using hw
    have hScaled : metricPair d.γ y (d.radius y • w) (d.radius y • w) ≤ (d.radius y)^2 := by
      rw [metricPair_smul_left,metricPair_smul_right]
      have hh := mul_le_mul_of_nonneg_left hUpper (sq_nonneg (d.radius y))
      nlinarith only [hh]
    exact hScaled.trans_lt hSq
  have hΓ0 : ∀ x ∈ Ω,‖connectionBilinear d.γ x‖ ≤ C := fun x hx => hd.1.connection_budget hKpos (by omega) hx
  have hΓ1 : ∀ x ∈ Ω,‖fderiv ℝ (connectionBilinear d.γ) x‖ ≤ D := fun x hx =>
    hd.1.connection_derivative_budget hΩ hKpos hm hx
  exact ⟨(hd.2.1.normalVerticalJacobian_sub_id_bound hΩ hd.1.1 hKpos hC hD hΓ0 hΓ1 hy _ hvInt hv1).trans hNear,
    hd.2.1.normalVerticalJacobian_inverse_bound hΩ hd.1.1 hKpos hC hD hΓ0 hΓ1 hy _ hvInt hv1 hNear⟩

end ShrinkingSpheres
