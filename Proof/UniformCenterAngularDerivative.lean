import Proof.NormalizedCenterDerivative
import Proof.FirstMetricNormalDensity
import Proof.EnlargedFramedEllipticity

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option maxSynthPendingDepth 15
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set
open scoped ContDiff
namespace ShrinkingSpheres

/-- The actual parallel-center velocity, in rescaled standard angular
    coordinates, differs from identity by O(radius squared) in C1. All constants
    use only the frozen background budgets, with no derivatives of the frame. -/
theorem uniform_normal_parallel_center_angular_C1 {Y Ω : Set X} (hY : IsOpen Y) (hΩ : IsOpen Ω)
    {m : ℕ} (hm : 3 ≤ m) (K ρ c₀ : ℝ) (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ)
    (hK : 1 ≤ K) (hρ : 0 < ρ) :
    ∃ η CG : ℝ,0 < η ∧ 0 ≤ CG ∧ ∀ floor,1 ≤ floor → ∀ ε,0 ≤ ε → ε ≤ η → ∀ d,
      Admissible Y Ω K ρ c₀ M Cj floor ε d → ∀ y ∈ Y,∀ z ∈ Metric.closedBall (0:X) 1,
      ‖normalizedParallelCenterJacobian d.γ d.expMap y
          (d.radius y • frameVector d.frame y z)-ContinuousLinearMap.id ℝ X‖ ≤ CG*(d.radius y)^2 ∧
      ‖fderiv ℝ (fun w => normalizedParallelCenterJacobian d.γ d.expMap y
          (d.radius y • frameVector d.frame y w)) z‖ ≤ CG*(d.radius y)^2 := by
  let C := 243*K*|M ⟨1,by omega⟩|
  let D := backgroundConnectionDerivativeBudget (show 2 ≤ m by omega) K M
  let E := backgroundSecondConnectionBudget hm K M
  let N := normalizedCenterDerivativeBudget K C D E
  have hKpos : 0 < K := zero_lt_one.trans_le hK
  have hC : 0 ≤ C := by dsimp only [C];positivity
  have hD : 0 ≤ D := by dsimp only [D,backgroundConnectionDerivativeBudget];positivity
  have hE : 0 ≤ E := by dsimp only [E,backgroundSecondConnectionBudget,secondConnectionBudget];positivity
  have hN : 0 ≤ N := by
    dsimp only [N,normalizedCenterDerivativeBudget,parallelCenterDerivativeErrorBudget,
      mixedParallelVariationBudget,mixedParallelForceBudget,parallelAccelerationBudget,
      parallelVelocityBudget,parallelVariationBudget,normalVelocitySecondErrorBudget,
      normalVariationErrorBudget,secondVelocityPrincipalErrorBudget,secondNormalVariationBudget]
    positivity
  obtain ⟨ηV,CV,hηV,hCV,hValue⟩ := uniform_normal_parallel_center_velocity hY hΩ
    (by omega) K ρ c₀ M Cj hK hρ
  obtain ⟨ηG,hηG,hControl⟩ := uniform_normal_control_on_disk (Y:=Y) hΩ
    (by omega) K ρ c₀ M Cj hK hρ 1 (by norm_num)
  refine ⟨min ηV (min ηG (ρ/2)),CV+N*K^2,lt_min hηV (lt_min hηG (half_pos hρ)),by positivity,?_⟩
  intro floor hf ε hε hSmall d hd y hy z hz
  have hCenter := hd.2.1.center_mem hy
  have hFrame := hd.1.2.2.2.2.2.2.2 y hCenter
  have hw := frameVector_mem_disk d.γ d.frame y z 1 hFrame hz
  have hPack := hControl floor hf ε hε
    (hSmall.trans ((min_le_right _ _).trans (min_le_left _ _))) d hd y hy (frameVector d.frame y z) hw
  have hr := (hd.2.2.2.2.1.2 y hy).1
  have hrε := (radius_bounds (d.radius y) (beta d.γ d.radius y) floor ε hr.le hf
    (hd.2.2.2.2.1.2 y hy).2.1 (hd.2.2.2.2.2 y hy).2).2.2
  have hrρ : d.radius y < ρ := hrε.trans_lt
    ((hSmall.trans ((min_le_right _ _).trans (min_le_right _ _))).trans_lt (half_lt_self hρ))
  have hSq : (d.radius y)^2 < (max ρ (d.radius y))^2 :=
    (sq_lt_sq₀ hr.le (hr.le.trans (le_max_right _ _))).2 (hrρ.trans_le (le_max_left _ _))
  have hStrict : metricPair d.γ y (d.radius y • frameVector d.frame y z)
      (d.radius y • frameVector d.frame y z) < (max ρ (d.radius y))^2 := by
    have hUpper : metricPair d.γ y (frameVector d.frame y z) (frameVector d.frame y z) ≤ 1 := by
      simpa only [disk,one_pow,mem_setOf_eq] using hw
    have hScaled : metricPair d.γ y (d.radius y • frameVector d.frame y z)
        (d.radius y • frameVector d.frame y z) ≤ (d.radius y)^2 := by
      rw [metricPair_smul_left,metricPair_smul_right]
      have hh := mul_le_mul_of_nonneg_left hUpper (sq_nonneg (d.radius y))
      nlinarith only [hh]
    exact hScaled.trans_lt hSq
  have hRadius : ContinuousAt (fun x => max ρ (d.radius x)) y :=
    continuousAt_const.max (((hd.2.2.2.2.1.1).contDiffAt (hY.mem_nhds hy)).continuousAt)
  have hΓ0 : ∀ x ∈ Ω,‖connectionBilinear d.γ x‖ ≤ C := fun x hx =>
    hd.1.connection_budget hKpos (by omega) hx
  have hΓ1 : ∀ x ∈ Ω,‖fderiv ℝ (connectionBilinear d.γ) x‖ ≤ D := fun x hx =>
    hd.1.connection_derivative_budget hΩ hKpos (by omega) hx
  have hΓ2 : ∀ x ∈ Ω,‖fderiv ℝ (fderiv ℝ (connectionBilinear d.γ)) x‖ ≤ E := fun x hx =>
    hd.1.connection_second_derivative_budget hΩ hKpos hm hx
  have hDerivative := hd.2.1.normalizedParallelCenterJacobian_derivative_bound hY hΩ hd.1.1 hKpos
    hC hD hE hΓ0 hΓ1 hΓ2 hy hRadius (d.radius y • frameVector d.frame y z) hStrict hPack.1.2 hPack.2.2.2.2
  have hENorm : ‖frameVectorLinear d.frame y‖ ≤ K := hd.1.1.norm_frameVectorLinear_le hK hCenter d.frame hFrame
  have hzNorm : ‖z‖ ≤ 1 := by simpa only [Metric.mem_closedBall,dist_zero_right] using hz
  have hVNorm : ‖d.radius y • frameVector d.frame y z‖ ≤ d.radius y*K := by
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos hr]
    have hWNorm : ‖frameVector d.frame y z‖ ≤ K :=
      ((frameVectorLinear d.frame y).le_opNorm z).trans
        ((mul_le_mul hENorm hzNorm (norm_nonneg z) hKpos.le).trans_eq (mul_one K))
    exact mul_le_mul_of_nonneg_left hWNorm hr.le
  have hInputNorm : ‖d.radius y • frameVectorLinear d.frame y‖ ≤ d.radius y*K := by
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos hr]
    exact mul_le_mul_of_nonneg_left hENorm hr.le
  have hSmooth := hd.2.1.contDiffAt_normalizedParallelCenterJacobian hy
    (d.radius y • frameVector d.frame y z) (interior_subset hPack.1.1)
  have hInput : HasFDerivAt (fun w => d.radius y • frameVector d.frame y w)
      (d.radius y • frameVectorLinear d.frame y) z := (frameVectorLinear d.frame y).hasFDerivAt.const_smul (d.radius y)
  have hOuter : HasFDerivAt (normalizedParallelCenterJacobian d.γ d.expMap y)
      (fderiv ℝ (normalizedParallelCenterJacobian d.γ d.expMap y)
        (d.radius y • frameVector d.frame y z)) (d.radius y • frameVector d.frame y z) :=
    (hSmooth.differentiableAt (by simp)).hasFDerivAt
  have hComp : HasFDerivAt (fun w => normalizedParallelCenterJacobian d.γ d.expMap y
      (d.radius y • frameVector d.frame y w))
      ((fderiv ℝ (normalizedParallelCenterJacobian d.γ d.expMap y)
        (d.radius y • frameVector d.frame y z)).comp (d.radius y • frameVectorLinear d.frame y)) z :=
    by simpa only [Function.comp_def] using hOuter.comp z hInput
  have hDf : fderiv ℝ (fun w => normalizedParallelCenterJacobian d.γ d.expMap y
      (d.radius y • frameVector d.frame y w)) z =
      (fderiv ℝ (normalizedParallelCenterJacobian d.γ d.expMap y)
        (d.radius y • frameVector d.frame y z)).comp (d.radius y • frameVectorLinear d.frame y) := hComp.fderiv
  constructor
  · exact (hValue floor hf ε hε (hSmall.trans (min_le_left _ _)) d hd y hy
      (frameVector d.frame y z) hw).trans (by gcongr;exact le_add_of_nonneg_right (by positivity))
  · rw [hDf]
    calc
      _ ≤ ‖fderiv ℝ (normalizedParallelCenterJacobian d.γ d.expMap y)
          (d.radius y • frameVector d.frame y z)‖*‖d.radius y • frameVectorLinear d.frame y‖ :=
        ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ (N*(d.radius y*K))*(d.radius y*K) := by
        gcongr
        exact hDerivative.trans (mul_le_mul_of_nonneg_left hVNorm hN)
      _ = (N*K^2)*(d.radius y)^2 := by ring
      _ ≤ (CV+N*K^2)*(d.radius y)^2 := by gcongr;linarith

end ShrinkingSpheres
