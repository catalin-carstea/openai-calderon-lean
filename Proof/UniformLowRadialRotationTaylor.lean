import Proof.UniformWeakConormalRotationTaylor
import Proof.ActualBoundaryRotationTaylorData
import Proof.ActualLowRadialTaylorPointData
import Proof.ActualRotatedLowInvertibility
import Proof.CommonSupportLowRadialTaylorDerivative
import Proof.EnlargedFramedEllipticity

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter MeasureTheory
open scoped ContDiff Topology ENNReal Matrix.Norms.Elementwise
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.EnergyBridge OAI.AnisotropicCalderon.DirichletFamily
open OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open OAI.AnisotropicCalderon.SphereHarmonic
open OAI.AnisotropicCalderon.SmoothSphereRotation
attribute [local instance] TauCeti.W1p0.instNormedAddCommGroup TauCeti.W1p0.instInnerProductSpace

/-- The actual low radial quadratic Taylor remainder has a genuine angle
    derivative bounded uniformly by the radius squared, for every admitted
    radius profile and arbitrary smooth orthonormal frame. All coefficient,
    first-model, inverse and point estimates use the same actual witnesses. -/
theorem uniform_actual_low_radial_rotation_taylor {Y Ω : Set X}
    (hY : IsOpen Y) (hΩ : IsOpen Ω) {m : ℕ} (hm : 4 ≤ m)
    (K ρ c₀ : ℝ) (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ) (hK : 1 ≤ K) (hρ : 0 < ρ) :
    ∃ η CL : ℝ,0 < η ∧ 0 ≤ CL ∧ ∀ floor,1 ≤ floor → ∀ ε,0 ≤ ε → ε ≤ η → ∀ d,
      Admissible Y Ω K ρ c₀ M Cj floor ε d → ∀ y ∈ Y,∀ i j : I,
      let c := firstMetricDensityFactor d.γ d.g₁ y
      let r := d.radius y
      let ell := firstDensityCenterLinearL d y
      ∃ a : ℝ × X → Mat,∃ ha : ContDiff ℝ ∞ a,∃ S : Set X,∃ hS : IsCompact S,
        ∃ hz : ∀ θ z,z ∉ S → a (θ,z) = 0,
      ∃ a1 : ℝ × X → Mat,∃ ha1 : ContDiff ℝ ∞ a1,∃ S1 : Set X,∃ hS1 : IsCompact S1,
        ∃ hz1 : ∀ θ z,z ∉ S1 → a1 (θ,z) = 0,
        (∀ θ z,z ∈ Metric.closedBall (0:X) 2 → a (θ,z) = coordinateRotationPrincipalFamily i j
          (fun v : ℝ × X => principalCoefficient (framedNormalMetric d.g₁ d.frame d.expMap y r) v.2) ((θ,0),z)) ∧
        (∀ θ z,z ∈ Metric.closedBall (0:X) 2 → a1 (θ,z) = ell (coordinateRotation i j θ z) • (1:Mat)) ∧
        DifferentiableAt ℝ (fun θ => commonSupportLowRadialErrorL a ha S hS hz θ-
          r • commonSupportLowFirstRadialL a1 ha1 S1 hS1 hz1 c θ) 0 ∧
        ‖fderiv ℝ (fun θ => commonSupportLowRadialErrorL a ha S hS hz θ-
          r • commonSupportLowFirstRadialL a1 ha1 S1 hS1 hz1 c θ) 0‖ ≤ CL*r^2 := by
  have hNTheorem := uniform_actual_weak_conormal_rotation_taylor hY hΩ hm K ρ c₀ M Cj hK hρ
  obtain ⟨ηN,CN,hηN,hCN,hNData⟩ := hNTheorem
  have hBTheorem := uniform_actual_boundary_rotation_taylor_data hY hΩ hm K ρ c₀ M Cj hK hρ
  obtain ⟨ηB,CB,hηB,hCB,hBData⟩ := hBTheorem
  have hPTheorem := uniform_actual_low_radial_taylor_point_data (Y:=Y) hΩ (by omega) K ρ c₀ M Cj hK hρ
  obtain ⟨ηP,CP,hηP,hCP,hPData⟩ := hPTheorem
  have hETheorem := uniform_enlarged_framed_normal_elliptic (Y:=Y) hΩ (by omega) K ρ c₀ M Cj hK hρ 2 (by norm_num)
  obtain ⟨ηE,hηE,hEData⟩ := hETheorem
  let CD := CN+CB+1
  let CL := lowRadialAngleDerivativeBudget K CP CD
  have hK0 : 0 ≤ K := le_trans zero_le_one hK
  have hCD : 0 ≤ CD := by dsimp [CD];positivity
  have hCL : 0 ≤ CL := lowRadialAngleDerivativeBudget_nonneg K CP CD hK0 hCP hCD
  refine ⟨min ηN (min ηB (min ηP (min ηE 1))),CL,
    lt_min hηN (lt_min hηB (lt_min hηP (lt_min hηE zero_lt_one))),hCL,?_⟩
  intro floor hf ε hε hSmall d hd y hy i j
  dsimp only
  let c := firstMetricDensityFactor d.γ d.g₁ y
  let r := d.radius y
  let H := framedNormalMetric d.g₁ d.frame d.expMap y r
  let KP := 4*K^2
  have hSN := hSmall.trans (min_le_left _ _)
  have hSB := hSmall.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hSP := hSmall.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hSE := hSmall.trans ((min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))))
  have hε1 : ε ≤ 1 := hSmall.trans ((min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))))
  have hNPoint := hNData floor hf ε hε hSN d hd y hy i j
  obtain ⟨a,ha,S,hS,hz,a1,ha1,S1,hS1,hz1,hRep,hRep1,hDN⟩ := hNPoint
  have hBPoint := hBData floor hf ε hε hSB d hd y hy i j a ha S hS hz a1 ha1 S1 hS1 hz1 hRep hRep1
  obtain ⟨hDM1,hDMQ,hDT,hDM,hDE1⟩ := hBPoint
  have hA0 (z : X) (hzB : z ∈ Metric.closedBall (0:X) 2) : a (0,z) = principalCoefficient H z := by
    simpa only [coordinateRotationPrincipalFamily_zero_angle] using hRep 0 z hzB
  have hA10 (z : X) (hzB : z ∈ Metric.closedBall (0:X) 2) : a1 (0,z) = firstDensityCenterLinearL d y z • (1:Mat) := by
    simpa only [coordinateRotation_zero] using hRep1 0 z hzB
  have hPPoint := hPData floor hf ε hε hSP d hd y hy a ha S hS hz a1 ha1 S1 hS1 hz1 hA0 hA10
  obtain ⟨hInvM0,hMINorm,hMDiff,hFirstPoint,hJPoint⟩ := hPPoint
  have hKP : 1 ≤ KP := by dsimp [KP];nlinarith [sq_nonneg (K-1)]
  have hEH : Elliptic (Metric.closedBall (0:X) 2) KP H := hEData floor hf ε hε hSE d hd y hy d.g₁ (by simp)
  have hInverseTheorem := actual_rotated_low_radial_invertibility H KP hKP hEH i j a ha S hS hz
    (fun θ z hzB => hRep θ z (unitBall_subset_closedBall_two hzB))
  obtain ⟨hWeak,hNormal,hSmoothL⟩ := hInverseTheorem
  have hr : 0 < r := (hd.2.2.2.2.1.2 y hy).1
  have hrε := (radius_bounds r (beta d.γ d.radius y) floor ε hr.le hf
    (hd.2.2.2.2.1.2 y hy).2.1 (hd.2.2.2.2.2 y hy).2).2.2
  have hr1 : r ≤ 1 := hrε.trans hε1
  have hc : 0 < c := firstMetricDensityFactor_pos _ _ _
  have hci : c⁻¹ ≤ K := hd.1.firstMetricDensityFactor_inverse_le (zero_lt_one.trans_le hK) (hd.2.1.center_mem hy)
  have hciAbs : |c⁻¹| ≤ K := by rw [abs_of_pos (inv_pos.mpr hc)];exact hci
  have hCNCD : CN ≤ CD := by dsimp [CD];linarith
  have hCBCD : CB ≤ CD := by dsimp [CD];linarith
  have hBound := norm_commonSupportLowRadial_first_remainder_derivative_le a a1 ha ha1 S S1 hS hS1 hz hz1
    c r K CP CD hc.ne' hr.le hr1 hK0 hCP hCD hciAbs hWeak hNormal hMINorm hMDiff hFirstPoint hJPoint
    (hDN.trans (mul_le_mul_of_nonneg_right hCNCD (sq_nonneg r)))
    (hDM1.trans hCBCD)
    (hDMQ.trans (mul_le_mul_of_nonneg_right hCBCD (sq_nonneg r)))
    (fun k => (hDT k).trans (mul_le_mul_of_nonneg_right hCBCD (sq_nonneg r)))
    (hDM.trans (mul_le_mul_of_nonneg_right hCBCD hr.le)) (hDE1.trans hCBCD)
  exact ⟨a,ha,S,hS,hz,a1,ha1,S1,hS1,hz1,hRep,hRep1,hBound⟩

end ShrinkingSpheres
