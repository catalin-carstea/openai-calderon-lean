import Proof.NormalCenterHorizontalVelocity
import Proof.EnlargedNormalInverse

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option maxSynthPendingDepth 15
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set
open scoped ContDiff
namespace ShrinkingSpheres

/-- The center velocity acting on the normalized unit-ball pullback, before
    multiplication by the reciprocal physical radius. -/
def normalizedParallelCenterJacobian (g : MetricField) (expMap : X × X → X) (y v : X) : X →L[ℝ] X :=
  (normalVerticalJacobian expMap y v).inverse.comp (normalParallelCenterJacobian g expMap y v)

lemma norm_inverse_comp_sub_id_le (J C : X →L[ℝ] X) (hJ : J.IsInvertible)
    (CI q : ℝ) (hCI : 0 ≤ CI) (hInv : ‖J.inverse‖ ≤ CI) (hDiff : ‖C-J‖ ≤ q) :
    ‖J.inverse.comp C-ContinuousLinearMap.id ℝ X‖ ≤ CI*q := by
  have hEq : J.inverse.comp C-ContinuousLinearMap.id ℝ X = J.inverse.comp (C-J) := by
    apply ContinuousLinearMap.ext
    intro a
    change J.inverse (C a)-a = J.inverse (C a-J a)
    rw [J.inverse.map_sub,hJ.inverse_apply_self]
  rw [hEq]
  exact (ContinuousLinearMap.opNorm_comp_le _ _).trans (mul_le_mul hInv hDiff (norm_nonneg _) hCI)

/-- A single threshold controls the genuine parallel-center Jacobi velocity on
    every admitted closed unit normal ball. Its linear error cancels and the
    remaining operator error is O(radius squared), without a frame jet budget. -/
theorem uniform_normal_parallel_center_velocity {Y Ω : Set X} (hY : IsOpen Y) (hΩ : IsOpen Ω)
    {m : ℕ} (hm : 2 ≤ m) (K ρ c₀ : ℝ) (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ)
    (hK : 1 ≤ K) (hρ : 0 < ρ) :
    ∃ η CG : ℝ,0 < η ∧ 0 ≤ CG ∧ ∀ floor,1 ≤ floor → ∀ ε,0 ≤ ε → ε ≤ η → ∀ d,
      Admissible Y Ω K ρ c₀ M Cj floor ε d → ∀ y ∈ Y,∀ w ∈ disk d.γ y 1,
      ‖normalizedParallelCenterJacobian d.γ d.expMap y (d.radius y • w)-ContinuousLinearMap.id ℝ X‖ ≤
        CG*(d.radius y)^2 := by
  let C := 243*K*|M ⟨1,by omega⟩|
  let D := backgroundConnectionDerivativeBudget hm K M
  let B := parallelAccelerationBudget K C D+normalVelocitySecondErrorBudget K C D
  have hKpos : 0 < K := zero_lt_one.trans_le hK
  have hC : 0 ≤ C := by dsimp [C];positivity
  have hD : 0 ≤ D := by dsimp [D,backgroundConnectionDerivativeBudget];positivity
  have hB : 0 ≤ B := by
    dsimp [B,parallelAccelerationBudget,parallelVelocityBudget,parallelVariationBudget,
      normalVelocitySecondErrorBudget,normalVariationErrorBudget];positivity
  obtain ⟨ηG,hηG,hControl⟩ := uniform_normal_control_on_disk (Y:=Y) hΩ hm K ρ c₀ M Cj hK hρ 1 (by norm_num)
  refine ⟨min ηG (ρ/2),2*B*K,lt_min hηG (half_pos hρ),by positivity,?_⟩
  intro floor hf ε hε hSmall d hd y hy w hw
  obtain ⟨⟨hvInt,hv1⟩,hImage,hSmooth,hNear,hInvNorm⟩ :=
    hControl floor hf ε hε (hSmall.trans (min_le_left _ _)) d hd y hy w hw
  have hr := (hd.2.2.2.2.1.2 y hy).1
  have hrε := (radius_bounds (d.radius y) (beta d.γ d.radius y) floor ε hr.le hf
    (hd.2.2.2.2.1.2 y hy).2.1 (hd.2.2.2.2.2 y hy).2).2.2
  have hrρ : d.radius y < ρ := hrε.trans_lt
    ((hSmall.trans (min_le_right _ _)).trans_lt (half_lt_self hρ))
  have hSq : (d.radius y)^2 < (max ρ (d.radius y))^2 :=
    (sq_lt_sq₀ hr.le (hr.le.trans (le_max_right _ _))).2
      (hrρ.trans_le (le_max_left _ _))
  have hStrict : metricPair d.γ y (d.radius y • w) (d.radius y • w) < (max ρ (d.radius y))^2 := by
    have hUpper : metricPair d.γ y w w ≤ 1 := by simpa only [disk,one_pow,mem_setOf_eq] using hw
    have hScaled : metricPair d.γ y (d.radius y • w) (d.radius y • w) ≤ (d.radius y)^2 := by
      rw [metricPair_smul_left,metricPair_smul_right]
      have hh := mul_le_mul_of_nonneg_left hUpper (sq_nonneg (d.radius y))
      nlinarith only [hh]
    exact hScaled.trans_lt hSq
  have hRadius : ContinuousAt (fun x => max ρ (d.radius x)) y :=
    continuousAt_const.max (((hd.2.2.2.2.1.1).contDiffAt (hY.mem_nhds hy)).continuousAt)
  have hΓ0 : ∀ x ∈ Ω,‖connectionBilinear d.γ x‖ ≤ C := fun x hx => hd.1.connection_budget hKpos (by omega) hx
  have hΓ1 : ∀ x ∈ Ω,‖fderiv ℝ (connectionBilinear d.γ) x‖ ≤ D := fun x hx =>
    hd.1.connection_derivative_budget hΩ hKpos hm hx
  have hDiff := hd.2.1.parallel_center_sub_vertical_bound hY hΩ hd.1.1 hKpos hC hD hΓ0 hΓ1 hy
    hRadius (d.radius y • w) hStrict hv1
  have hJInv := hd.2.1.normalVerticalJacobian_isInvertible hy (d.radius y • w) (interior_subset hvInt)
  have hError := norm_inverse_comp_sub_id_le _ _ hJInv 2 (B*‖d.radius y • w‖^2)
    (by norm_num) hInvNorm hDiff
  have hwSq := hd.1.1.disk_norm_sq_bound hKpos (hd.2.1.center_mem hy) hw
  have hvSq : ‖d.radius y • w‖^2 ≤ (d.radius y)^2*K := by
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos hr,mul_pow]
    exact mul_le_mul_of_nonneg_left hwSq (sq_nonneg _)
  change ‖(normalVerticalJacobian d.expMap y (d.radius y • w)).inverse.comp
      (normalParallelCenterJacobian d.γ d.expMap y (d.radius y • w))-ContinuousLinearMap.id ℝ X‖ ≤
        (2*B*K)*(d.radius y)^2
  calc
    _ ≤ 2*(B*‖d.radius y • w‖^2) := hError
    _ ≤ 2*(B*((d.radius y)^2*K)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hvSq hB) (by norm_num)
    _ = _ := by ring

end ShrinkingSpheres
