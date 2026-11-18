import Proof.LowRadialCoefficientCongruence
import Proof.FirstMetricNormalCenterCoefficient
import Proof.UniformBoundaryCoefficientData

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
open OAI.AnisotropicCalderon.NativeBoundaryCoefficientFamilies
attribute [local instance] TauCeti.W1p0.instNormedAddCommGroup TauCeti.W1p0.instInnerProductSpace

/-- The genuine point inverse and quadratic low radial Taylor norms transfer
    to any same actual compact coefficient and first-model angle witnesses. -/
theorem uniform_actual_low_radial_taylor_point_data {Y Ω : Set X} (hΩ : IsOpen Ω)
    {m : ℕ} (hm : 3 ≤ m) (K ρ c₀ : ℝ) (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ)
    (hK : 1 ≤ K) (hρ : 0 < ρ) :
    ∃ η C : ℝ,0 < η ∧ 0 ≤ C ∧ ∀ floor,1 ≤ floor → ∀ ε,0 ≤ ε → ε ≤ η → ∀ d,
      Admissible Y Ω K ρ c₀ M Cj floor ε d → ∀ y ∈ Y,
      let c := firstMetricDensityFactor d.γ d.g₁ y
      let r := d.radius y
      let ell := firstDensityCenterLinearL d y
      ∀ a : ℝ × X → Mat,∀ ha : ContDiff ℝ ∞ a,∀ S : Set X,∀ hS : IsCompact S,
      ∀ hz : ∀ θ z,z ∉ S → a (θ,z) = 0,
      ∀ a1 : ℝ × X → Mat,∀ ha1 : ContDiff ℝ ∞ a1,∀ S1 : Set X,∀ hS1 : IsCompact S1,
      ∀ hz1 : ∀ θ z,z ∉ S1 → a1 (θ,z) = 0,
      (∀ z,z ∈ Metric.closedBall (0:X) 2 → a (0,z) = principalCoefficient
        (framedNormalMetric d.g₁ d.frame d.expMap y r) z) →
      (∀ z,z ∈ Metric.closedBall (0:X) 2 → a1 (0,z) = ell z • (1:Mat)) →
      let N := negativeBoundaryCoefficientMulL (normalCoefficientJetsFamily a ha S hS hz 0)
      N.IsInvertible ∧ ‖N.inverse‖ ≤ C ∧
      ‖N-c • ContinuousLinearMap.id ℝ (SphereSobolev (-(1/2:ℝ)))‖ ≤ C*r ∧
      ‖commonSupportLowFirstRadialL a1 ha1 S1 hS1 hz1 c 0‖ ≤ C ∧
      ‖commonSupportLowRadialErrorL a ha S hS hz 0-r • commonSupportLowFirstRadialL a1 ha1 S1 hS1 hz1 c 0‖ ≤ C*r^2 := by
  have hBoundaryTheorem := uniform_actual_boundary_coefficient_data (Y:=Y) hΩ hm K ρ c₀ M Cj hK hρ
  obtain ⟨ηI,CI,CM,CT,hηI,hCI,hCM,hCT,hBoundary⟩ := hBoundaryTheorem
  have hLowTheorem := uniform_actual_low_radial_taylor (Y:=Y) hΩ hm K ρ c₀ M Cj hK hρ
  obtain ⟨ηL,CB,CL,hηL,hCB,hCL,hLow⟩ := hLowTheorem
  let C := CI+CM+CB+CL+1
  have hC : 0 ≤ C := by dsimp [C];positivity
  refine ⟨min ηI ηL,C,lt_min hηI hηL,hC,?_⟩
  intro floor hf ε hε hSmall d hd y hy
  dsimp only
  intro a ha S hS hz a1 ha1 S1 hS1 hz1 hA0 hA10
  let c := firstMetricDensityFactor d.γ d.g₁ y
  let r := d.radius y
  let H := framedNormalMetric d.g₁ d.frame d.expMap y r
  let ell := firstDensityCenterLinearL d y
  let F := commonSupportMatrixFamily 2 a ha S hS hz 0
  let N := negativeBoundaryCoefficientMulL (normalCoefficientJetsFamily a ha S hS hz 0)
  have hr : 0 < r := (hd.2.2.2.2.1.2 y hy).1
  have hI := hBoundary floor hf ε hε (hSmall.trans (min_le_left _ _)) d hd y hy
  obtain ⟨GI,cI,hcIBounds,hcI,hScalarI,hRepI,hUEI,hInvI,hDiffI,hTangI⟩ := hI
  have hScalarC := hd.firstMetric_normal_principal_center (zero_lt_one.trans_le hK) hy r
  have hcEq : cI = c := by
    have h := congrArg (fun A : Mat => A (0:I) (0:I)) (hScalarI.symm.trans hScalarC)
    simpa only [Matrix.smul_apply,smul_eq_mul,Matrix.one_apply,ite_true,mul_one] using h
  have hFieldI (z : X) (hzB : z ∈ Metric.closedBall (0:X) 2) : coefficientMatrixField 2 GI z = principalCoefficient H z := by
    ext k l
    exact (hRepI z hzB k l).eq_of_nhds
  have hSphere (G : SmoothCoefficientMatrix 2)
      (hG : ∀ z ∈ Metric.closedBall (0:X) 2,coefficientMatrixField 2 G z = principalCoefficient H z) :
      ∀ w : UnitSphere,coefficientMatrixField 2 F w.val = coefficientMatrixField 2 G w.val := by
    intro w
    have hw : w.val ∈ Metric.closedBall (0:X) 2 := Metric.closedBall_subset_closedBall (by norm_num)
      (Metric.sphere_subset_closedBall w.property)
    change coefficientMatrixField 2 (commonSupportMatrixFamily 2 a ha S hS hz 0) w.val = _
    rw [coefficientMatrixField_commonSupportMatrixFamily]
    exact (hA0 w.val hw).trans (hG w.val hw).symm
  have hNEq : N = negativeBoundaryCoefficientMulL (normalCoefficientJet GI) := by
    rw [show N = negativeBoundaryCoefficientMulL (normalCoefficientJet F) from
      commonSupport_negative_normal_multiplier_eq a ha S hS hz 0]
    exact negativeBoundaryCoefficientMulL_congr_sphere _ _ (normalCoefficientJet_value_congr_sphere F GI (hSphere GI hFieldI))
  have hNInv : N.IsInvertible := by
    rw [hNEq]
    exact negativeNormalCoefficient_isInvertible GI (normalCoefficientJet GI) (coefficientSmoothData_normalCoefficientJet GI) _ _ hUEI
  have hNI : ‖N.inverse‖ ≤ CI := by rw [hNEq];exact hInvI
  have hNDiff : ‖N-c • ContinuousLinearMap.id ℝ (SphereSobolev (-(1/2:ℝ)))‖ ≤ CM*r := by
    rw [hNEq,← hcEq]
    exact hDiffI
  have hL := hLow floor hf ε hε (hSmall.trans (min_le_right _ _)) d hd y hy
  obtain ⟨F0,FL,FL1,e,hFL1,hF0,hRepL,hRepL1,hStrongL,hStrongL0,hMLInv,hBPoint,hJPoint⟩ := hL
  have hFieldL (z : X) (hzB : z ∈ Metric.closedBall (0:X) 2) : coefficientMatrixField 2 FL z = principalCoefficient H z := by
    ext k l
    exact (hRepL z hzB k l).eq_of_nhds
  have hFirstPoint (z : X) (hzB : z ∈ Metric.closedBall (0:X) 2) : a1 (0,z) = coefficientMatrixField 2 FL1 z := by
    rw [hA10 z hzB]
    ext k l
    exact (hRepL1 z hzB k l).eq_of_nhds.symm
  have hFirstEq := commonSupport_lowFirstRadial_eq_of_coefficient a1 ha1 S1 hS1 hz1 0 c FL1 hFL1 hFirstPoint
  have hLowEq : commonSupportLowRadialErrorL a ha S hS hz 0 =
      actualLowRadialErrorL (principalCoefficient H) e.coefficient_bound FL :=
    actualLowRadialError_congr_coefficients (commonSupportEnergyMemLp a ha 0) e.coefficient_bound F FL
      (fun z hzB => hA0 z (unitBall_subset_closedBall_two hzB)) (hSphere FL hFieldL)
  have hB : ‖commonSupportLowFirstRadialL a1 ha1 S1 hS1 hz1 c 0‖ ≤ CB := by
    rw [hFirstEq]
    exact hBPoint
  have hJ : ‖commonSupportLowRadialErrorL a ha S hS hz 0-r • commonSupportLowFirstRadialL a1 ha1 S1 hS1 hz1 c 0‖ ≤ CL*r^2 := by
    rw [hLowEq,hFirstEq]
    exact hJPoint
  have hCInv : CI ≤ C := by dsimp [C];linarith
  have hCM : CM ≤ C := by dsimp [C];linarith
  have hCB' : CB ≤ C := by dsimp [C];linarith
  have hCL' : CL ≤ C := by dsimp [C];linarith
  exact ⟨hNInv,hNI.trans hCInv,hNDiff.trans (mul_le_mul_of_nonneg_right hCM hr.le),
    hB.trans hCB',hJ.trans (mul_le_mul_of_nonneg_right hCL' (sq_nonneg r))⟩

end ShrinkingSpheres
