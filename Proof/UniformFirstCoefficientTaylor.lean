import Proof.UniformFirstDensityTaylor
import Proof.UniformQuadraticReferenceCoefficientDerivative
import Proof.UniformQuadraticReferenceCoefficient
import Proof.ScalarProductAffineError

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option maxSynthPendingDepth 15
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter
open scoped ContDiff Topology
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.EnergyBridge

/-- A scalar affine first radial model for the actual first-metric divergence
    coefficient, with one common quadratic C1 remainder. -/
theorem uniform_first_coefficient_taylor {Y Ω : Set X} (hΩ : IsOpen Ω)
    {m : ℕ} (hm : 3 ≤ m) (K ρ c₀ : ℝ) (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ)
    (hK : 1 ≤ K) (hρ : 0 < ρ) (L : ℝ) (hL : 0 ≤ L) :
    ∃ η Q : ℝ,0 < η ∧ 0 ≤ Q ∧ ∀ floor,1 ≤ floor → ∀ ε,0 ≤ ε → ε ≤ η → ∀ d,
      Admissible Y Ω K ρ c₀ M Cj floor ε d → ∀ y ∈ Y,
      ∀ z ∈ Metric.closedBall (0:X) L,∀ i j,
      let A := principalCoefficient (framedNormalMetric d.g₁ d.frame d.expMap y (d.radius y))
      let c := firstMetricDensityFactor d.γ d.g₁ y
      let ℓ := firstDensityCenterLinearL d y
      |A z i j-(c+d.radius y*ℓ z)*(1:Mat) i j| ≤ Q*(d.radius y)^2 ∧
      ‖fderiv ℝ (fun w => A w i j) z-(d.radius y*(1:Mat) i j) • ℓ‖ ≤ Q*(d.radius y)^2 := by
  obtain ⟨ηT,QT,hηT,hQT,hTaylor⟩ := uniform_first_density_taylor
    (Y:=Y) hΩ (by omega) K ρ c₀ M Cj hK hρ L hL
  obtain ⟨η0,hη0,h0⟩ := uniform_framed_reference_coefficient_quadratic
    (Y:=Y) hΩ (by omega) K ρ c₀ M Cj hK hρ L hL
  obtain ⟨η1,hη1,h1⟩ := uniform_framed_reference_coefficient_derivative_quadratic
    (Y:=Y) hΩ hm K ρ c₀ M Cj hK hρ L hL
  obtain ⟨ηE,hηE,hE⟩ := uniform_enlarged_framed_normal_elliptic
    (Y:=Y) hΩ (by omega) K ρ c₀ M Cj hK hρ (L+1) (by positivity)
  obtain ⟨ηG,hηG,hGeometry⟩ := uniform_normal_control_on_disk
    (Y:=Y) hΩ (by omega) K ρ c₀ M Cj hK hρ (L+1) (by positivity)
  let B0 := |normalReferenceCoefficientClosenessBudget (by omega : 2 ≤ m) K M L|
  let B1 := |normalReferenceCoefficientAngularDerivativeBudget hm K M L|
  let P := K^3*|M ⟨1,by omega⟩|
  let G := QT+P
  let Q0 := QT+K*B0
  let Q1 := QT+K*B1+B0*G
  let Q := Q0+Q1
  have hKpos : 0 < K := zero_lt_one.trans_le hK
  have hB0 : 0 ≤ B0 := abs_nonneg _
  have hB1 : 0 ≤ B1 := abs_nonneg _
  have hP : 0 ≤ P := by dsimp [P];positivity
  have hG : 0 ≤ G := add_nonneg hQT hP
  have hQ0 : 0 ≤ Q0 := by dsimp [Q0];positivity
  have hQ1 : 0 ≤ Q1 := by dsimp [Q1];positivity
  have hQ : 0 ≤ Q := add_nonneg hQ0 hQ1
  let η := min (min ηT η0) (min η1 (min ηE (min ηG 1)))
  refine ⟨η,Q,lt_min (lt_min hηT hη0) (lt_min hη1 (lt_min hηE (lt_min hηG zero_lt_one))),hQ,?_⟩
  intro floor hf ε hε hSmall d hd y hy z hz i j
  dsimp only
  have hST := hSmall.trans ((min_le_left _ _).trans (min_le_left _ _))
  have hS0 := hSmall.trans ((min_le_left _ _).trans (min_le_right _ _))
  have hS1 := hSmall.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hSE := hSmall.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hSG := hSmall.trans ((min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))))
  have hε1 : ε ≤ 1 := hSmall.trans ((min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))))
  obtain ⟨hc,hcK,hLn,hTaylorY⟩ := hTaylor floor hf ε hε hST d hd y hy
  obtain ⟨hVal,hDeriv⟩ := hTaylorY z hz
  let q := framedFirstDensityFactor d y
  let H := framedNormalMetric d.γ d.frame d.expMap y (d.radius y)
  let s := fun w => principalCoefficient H w i j
  let c := firstMetricDensityFactor d.γ d.g₁ y
  let ℓ := firstDensityCenterLinearL d y
  let r := d.radius y
  have hr : 0 < r := (hd.2.2.2.2.1.2 y hy).1
  have hrε := (radius_bounds r (beta d.γ d.radius y) floor ε hr.le hf
    (hd.2.2.2.2.1.2 y hy).2.1 (hd.2.2.2.2.2 y hy).2).2.2
  have hr1 : r ≤ 1 := hrε.trans hε1
  have hrSq1 : r^2 ≤ 1 := by nlinarith only [mul_le_mul hr1 hr1 hr.le zero_le_one]
  have hEll : Elliptic (Metric.closedBall (0:X) (L+1)) (4*K^2) H :=
    hE floor hf ε hε hSE d hd y hy d.γ (by simp)
  have hEllOpen : Elliptic (Metric.ball (0:X) (L+1)) (4*K^2) H :=
    ⟨fun a b => (hEll.1 a b).mono Metric.ball_subset_closedBall,
      fun w hw => hEll.2 w (Metric.ball_subset_closedBall hw)⟩
  have hzOpen : z ∈ Metric.ball (0:X) (L+1) := by
    change dist z 0 < L+1
    change dist z 0 ≤ L at hz
    linarith
  have hPoint (w : X) (hw : w ∈ Metric.ball (0:X) (L+1)) :
      d.expMap (y,r • frameVector d.frame y w) ∈ Ω := by
    have hFrame := hd.1.2.2.2.2.2.2.2 y (hd.2.1.center_mem hy)
    exact (hGeometry floor hf ε hε hSG d hd y hy _
      (frameVector_mem_disk d.γ d.frame y w (L+1) hFrame (Metric.ball_subset_closedBall hw))).2.1
  have hF := ((hd.1.firstMetricDensityFactor_smooth hKpos).contDiffAt (hΩ.mem_nhds (hPoint z hzOpen))).differentiableAt (by simp)
  have hFrame := hd.1.2.2.2.2.2.2.2 y (hd.2.1.center_mem hy)
  have hPack := hGeometry floor hf ε hε hSG d hd y hy _
    (frameVector_mem_disk d.γ d.frame y z (L+1) hFrame (Metric.ball_subset_closedBall hzOpen))
  have hSlice := hd.2.1.hasFDerivAt_velocity_slice hy (r • frameVector d.frame y z) (interior_subset hPack.1.1)
  have hScale : HasFDerivAt (fun w => r • frameVector d.frame y w) (r • frameVectorLinear d.frame y) z := by
    convert (r • frameVectorLinear d.frame y).hasFDerivAt using 1
    funext w
    rfl
  have hEndpoint := hSlice.comp z hScale
  have hqFD := hF.hasFDerivAt.comp z hEndpoint
  have hsDiff : DifferentiableAt ℝ s z :=
    (contDiffOn_pi.mp (contDiffOn_pi.mp (hEllOpen.contDiffOn_principalCoefficient (by positivity)) i) j).contDiffAt
      (Metric.isOpen_ball.mem_nhds hzOpen) |>.differentiableAt (by simp)
  have hq0 : |q z| ≤ K := by
    change |firstMetricDensityFactor d.γ d.g₁ (d.expMap (y,r • frameVector d.frame y z))| ≤ K
    rw [abs_of_pos (firstMetricDensityFactor_pos _ _ _)]
    exact hd.1.firstMetricDensityFactor_le hKpos (hPoint z hzOpen)
  have hq1 : ‖fderiv ℝ q z‖ ≤ G := by
    calc
      _ ≤ ‖fderiv ℝ q z-r • ℓ‖+‖r • ℓ‖ := norm_le_norm_sub_add _ _
      _ ≤ QT*r^2+r*P := add_le_add hDeriv (by
        rw [norm_smul,Real.norm_eq_abs,abs_of_pos hr]
        exact mul_le_mul_of_nonneg_left hLn hr.le)
      _ ≤ QT+P := add_le_add (by nlinarith only [mul_le_mul_of_nonneg_left hrSq1 hQT])
        (by nlinarith only [mul_le_mul_of_nonneg_right hr1 hP])
  have hs0 : |s z-(1:Mat) i j| ≤ B0*r^2 :=
    (h0 floor hf ε hε hS0 d hd y hy z hz i j).trans
      (mul_le_mul_of_nonneg_right (le_abs_self _) (sq_nonneg _))
  have hs1 : ‖fderiv ℝ s z‖ ≤ B1*r^2 :=
    (h1 floor hf ε hε hS1 d hd y hy z hz i j).trans
      (mul_le_mul_of_nonneg_right (le_abs_self _) (sq_nonneg _))
  have hδ : |(1:Mat) i j| ≤ 1 := by simp only [Matrix.one_apply];split_ifs <;> norm_num
  have hb := scalar_product_affine_error q s z c r ((1:Mat) i j) K QT B0 B1 G ℓ
    hqFD.differentiableAt hsDiff hKpos.le hQT hB0 hB1 hG hδ hq0 hq1 hVal hDeriv hs0 hs1
  have hEq : (fun w => principalCoefficient (framedNormalMetric d.g₁ d.frame d.expMap y r) w i j) =ᶠ[𝓝 z]
      (fun w => q w*s w) := by
    filter_upwards [Metric.isOpen_ball.mem_nhds hzOpen] with w hw
    have hDet := isUnit_iff_ne_zero.mpr (hEllOpen.posDef (by positivity) hw).det_pos.ne'
    have hCoeff := hd.framed_firstMetric_density_coefficient hKpos (hPoint w hw) hDet
    exact congrArg (fun A : Mat => A i j) hCoeff
  refine ⟨?_,?_⟩
  · rw [hEq.eq_of_nhds]
    exact hb.1.trans (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right hQ1) (sq_nonneg _))
  · rw [hEq.fderiv_eq]
    exact hb.2.trans (mul_le_mul_of_nonneg_right (le_add_of_nonneg_left hQ0) (sq_nonneg _))

end ShrinkingSpheres
