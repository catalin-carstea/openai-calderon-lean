import Proof.ParallelNormalizedCoefficientCenter
import Proof.UniformParallelReferenceCoefficientCenter
import Proof.UniformQuadraticReferenceCoefficientDerivative

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set
open scoped ContDiff Matrix.Norms.Operator
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.EnergyBridge

def uniformParallelFirstCoefficientCenterBudget {m : ℕ} (hm : 5 ≤ m) (K : ℝ) (M : Fin (m+1) → ℝ) (Z : ℝ) : ℝ :=
  parallelNormalizedCoefficientCenterBudget hm K M K Z
    |normalReferenceCoefficientClosenessBudget (by omega) K M Z|
    |parallelReferenceCoefficientCenterBudget hm K M Z|

def uniformParallelFirstCoefficientMixedBudget {m : ℕ} (hm : 5 ≤ m) (K : ℝ) (M : Fin (m+1) → ℝ) (Z : ℝ) : ℝ :=
  parallelNormalizedCoefficientMixedBudget hm K M K Z
    |normalReferenceCoefficientClosenessBudget (by omega) K M Z|
    |parallelReferenceCoefficientCenterBudget hm K M Z|
    |normalReferenceCoefficientAngularDerivativeBudget (by omega) K M Z|
    |parallelReferenceCoefficientMixedBudget hm K M Z|

/-- Unconditional uniform quadratic center C1 estimates for the true
    normalized first-metric divergence coefficient, for every admitted radius. -/
theorem uniform_parallel_first_coefficient_center {Y Ω : Set X} (hY : IsOpen Y) (hΩ : IsOpen Ω)
    {m : ℕ} (hm : 5 ≤ m) (K ρ c₀ : ℝ) (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ)
    (hK : 1 ≤ K) (hρ : 0 < ρ) (Z : ℝ) (hZ : 0 ≤ Z) :
    ∃ η : ℝ,0 < η ∧ ∀ floor,1 ≤ floor → ∀ ε,0 ≤ ε → ε ≤ η → ∀ d,
      Admissible Y Ω K ρ c₀ M Cj floor ε d → ∀ y ∈ Y,∀ a : X,∀ z ∈ Metric.closedBall (0:X) Z,
      ∀ b : X,∀ i j,
      let F := fun p => parallelNormalizedFirstCoefficientRemainder d.γ d.g₁ d.expMap y a (d.radius y)
        (frameVectorLinear d.frame y) p i j
      |fderiv ℝ F (0,z) (1,0)| ≤ uniformParallelFirstCoefficientCenterBudget hm K M Z*(d.radius y)^2*‖a‖ ∧
      |fderiv ℝ (fderiv ℝ F) (0,z) (0,b) (1,0)| ≤
        uniformParallelFirstCoefficientMixedBudget hm K M Z*(d.radius y)^2*‖a‖*‖b‖ := by
  obtain ⟨ηG,hηG,hGeometry⟩ := uniform_normal_control_on_disk (Y:=Y) hΩ (by omega) K ρ c₀ M Cj hK hρ Z hZ
  obtain ⟨ηC,hηC,hCenter⟩ := uniform_parallel_reference_coefficient_center hY hΩ hm K ρ c₀ M Cj hK hρ Z hZ
  obtain ⟨ηV,hηV,hValue⟩ := uniform_framed_reference_coefficient_quadratic (Y:=Y) hΩ (by omega) K ρ c₀ M Cj hK hρ Z hZ
  obtain ⟨ηD,hηD,hAngular⟩ := uniform_framed_reference_coefficient_derivative_quadratic (Y:=Y) hΩ (by omega) K ρ c₀ M Cj hK hρ Z hZ
  obtain ⟨ηE,hηE,hElliptic⟩ := uniform_enlarged_framed_normal_elliptic (Y:=Y) hΩ (by omega) K ρ c₀ M Cj hK hρ Z hZ
  refine ⟨min ηG (min ηC (min ηV (min ηD (min ηE 1)))),
    lt_min hηG (lt_min hηC (lt_min hηV (lt_min hηD (lt_min hηE zero_lt_one)))),?_⟩
  intro floor hf ε hε hSmall d hd y hy a z hz b i j
  dsimp only
  rcases le_min_iff.mp hSmall with ⟨hεG,hRest⟩
  rcases le_min_iff.mp hRest with ⟨hεC,hRest⟩
  rcases le_min_iff.mp hRest with ⟨hεV,hRest⟩
  rcases le_min_iff.mp hRest with ⟨hεD,hRest⟩
  rcases le_min_iff.mp hRest with ⟨hεE,hε1⟩
  let r := d.radius y
  let L := frameVectorLinear d.frame y
  let G := parallelFrameNormalMetric d.γ d.expMap y a r L
  let H := fun p => matrixFamilyCoefficient G p i j
  let H0 := |normalReferenceCoefficientClosenessBudget (by omega : 2 ≤ m) K M Z|
  let HC := |parallelReferenceCoefficientCenterBudget hm K M Z|
  let HZ := |normalReferenceCoefficientAngularDerivativeBudget (by omega : 3 ≤ m) K M Z|
  let HM := |parallelReferenceCoefficientMixedBudget hm K M Z|
  have hKpos : 0 < K := zero_lt_one.trans_le hK
  have hCenterMem := hd.2.1.center_mem hy
  have hFrame := hd.1.2.2.2.2.2.2.2 y hCenterMem
  have hL : ‖L‖ ≤ K := hd.1.1.norm_frameVectorLinear_le hK hCenterMem d.frame hFrame
  have hr : 0 < r := (hd.2.2.2.2.1.2 y hy).1
  have hrε : r ≤ ε := (radius_bounds r (beta d.γ d.radius y) floor ε hr.le hf
    (hd.2.2.2.2.1.2 y hy).2.1 (hd.2.2.2.2.2 y hy).2).2.2
  have hr1 : r ≤ 1 := hrε.trans hε1
  have hzNorm : ‖z‖ ≤ Z := by simpa only [Metric.mem_closedBall,dist_zero_right] using hz
  have hw := frameVector_mem_disk d.γ d.frame y z Z hFrame hz
  have hPack := hGeometry floor hf ε hε hεG d hd y hy (L z) hw
  have hRadius : ContinuousOn (fun x => max ρ (d.radius x)) Y := by
    intro x hx
    have hConst : ContinuousAt (fun _ : X => ρ) x := continuousAt_const
    have hMax : ContinuousAt (fun t : X => max ρ (d.radius t)) x :=
      hConst.max ((hd.2.2.2.2.1.1.contDiffAt (hY.mem_nhds hx)).continuousAt)
    exact hMax.continuousWithinAt
  have hStrict : metricPair d.γ y (r • L z) (r • L z) < (max ρ r)^2 :=
    metricPair_lt_of_mem_interior_disk d.γ y (r • L z) (max ρ r)
      (hρ.trans_le (le_max_left _ _)) hPack.1.1
  have hEll : Elliptic (Metric.closedBall (0:X) Z) (4*K^2)
      (framedNormalMetric d.γ d.frame d.expMap y r) :=
    hElliptic floor hf ε hε hεE d hd y hy d.γ (by simp)
  have hAt (w : X) : G (0,w) = framedNormalMetric d.γ d.frame d.expMap y r w :=
    parallelFrameNormalMetric_zero d.γ d.expMap y a r d.frame w
  have hCoeffAt (w : X) : H (0,w) = principalCoefficient (framedNormalMetric d.γ d.frame d.expMap y r) w i j := by
    change Real.sqrt (G (0,w)).det*(G (0,w))⁻¹ i j = _
    rw [hAt]
    rfl
  have hPos : 0 < (G (0,z)).det := by rw [hAt];exact (hEll.posDef (by positivity) hz).det_pos
  have hHv : |H (0,z)-(1:Mat) i j| ≤ H0*r^2 := by
    rw [hCoeffAt]
    exact (hValue floor hf ε hε hεV d hd y hy z hz i j).trans
      (mul_le_mul_of_nonneg_right (le_abs_self _) (sq_nonneg r))
  have hRef := hCenter floor hf ε hε hεC d hd y hy a z hz b i j
  have hHc : |fderiv ℝ H (0,z) (1,0)| ≤ HC*r^2*‖a‖ := hRef.1.trans
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_abs_self _) (sq_nonneg r)) (norm_nonneg a))
  have hHm : |fderiv ℝ (fderiv ℝ H) (0,z) (0,b) (1,0)| ≤ HM*r^2*‖a‖*‖b‖ := hRef.2.trans
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (le_abs_self _) (sq_nonneg r)) (norm_nonneg a)) (norm_nonneg b))
  obtain ⟨S,hS,hHere,hGS,hDet⟩ := hd.2.1.exists_parallel_frame_metric_domain hΩ hd.1.1 hy a r L z hStrict.le hPos
  have hNe (p) (hp : p ∈ S) : (G p).det ≠ 0 := (hDet p hp).ne'
  have hHS : ContDiffOn ℝ ∞ H S := (contDiffOn_matrixFamily_density G hGS hNe).mul
    (contDiffOn_matrixFamily_inverse_entry G hGS hNe i j)
  have hH : ContDiffAt ℝ ∞ H (0,z) := hHS.contDiffAt (hS.mem_nhds hHere)
  have hSlice := (hH.differentiableAt (by simp)).hasFDerivAt.comp z
    ((hasFDerivAt_const (0:ℝ) z).prodMk (hasFDerivAt_id z))
  have hFun : (fun w => H (0,w)) = fun w => principalCoefficient (framedNormalMetric d.γ d.frame d.expMap y r) w i j := by
    funext w;exact hCoeffAt w
  simp only [Function.comp_def] at hSlice
  have hSliceEq := congrArg (fun D : X →L[ℝ] ℝ => D b) hSlice.fderiv
  rw [hFun] at hSliceEq
  have hAngularEq : fderiv ℝ H (0,z) (0,b) =
      fderiv ℝ (fun w => principalCoefficient (framedNormalMetric d.γ d.frame d.expMap y r) w i j) z b := by
    simpa only [ContinuousLinearMap.comp_apply,ContinuousLinearMap.prod_apply,ContinuousLinearMap.id_apply,zero_apply] using hSliceEq.symm
  have hHz : |fderiv ℝ H (0,z) (0,b)| ≤ HZ*r^2*‖b‖ := by
    rw [hAngularEq,← Real.norm_eq_abs]
    have hb := ((fderiv ℝ (fun w => principalCoefficient (framedNormalMetric d.γ d.frame d.expMap y r) w i j) z).le_opNorm b).trans
      (mul_le_mul_of_nonneg_right (hAngular floor hf ε hε hεD d hd y hy z hz i j) (norm_nonneg b))
    exact hb.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_abs_self _) (sq_nonneg r)) (norm_nonneg b))
  exact hd.1.parallel_normalized_coefficient_center_bounds hY hΩ hKpos hm hd.2.1 hRadius hy a r hr.le hr1 L K Z hKpos.le hZ hL z hzNorm
    hStrict hPack.1.2 b i j hPos H0 HC HZ HM (abs_nonneg _) (abs_nonneg _) (abs_nonneg _) (abs_nonneg _) hHv hHc hHz hHm

end ShrinkingSpheres
