import Proof.UniformLowRadialRotationTaylor
import Proof.UniformHighRadialRotationTaylor
import Proof.RotatedRadialTaylorCompatibility
import Proof.CompatibleEndpointDerivative
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

/-- The genuine actual radial Taylor angle derivative has a uniform
    H1-to-L2 midpoint operator bound of order radius squared. The high
    derivative and its whole-angle geometric representatives are retained. -/
theorem uniform_actual_midpoint_radial_rotation_derivative {Y Ω : Set X}
    (hY : IsOpen Y) (hΩ : IsOpen Ω) {m : ℕ} (hm : 4 ≤ m)
    (K ρ c₀ : ℝ) (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ) (hK : 1 ≤ K) (hρ : 0 < ρ) :
    ∃ η CM : ℝ,∃ F0 : SmoothCoefficientMatrix 2,0 < η ∧ 0 ≤ CM ∧
      (∀ z ∈ Metric.closedBall (0:X) 2,coefficientMatrixField 2 F0 z = 1) ∧
      ∀ floor,1 ≤ floor → ∀ ε,0 ≤ ε → ε ≤ η → ∀ d,
      Admissible Y Ω K ρ c₀ M Cj floor ε d → ∀ y ∈ Y,∀ i j : I,
      let c := firstMetricDensityFactor d.γ d.g₁ y
      let r := d.radius y
      let ell := firstDensityCenterLinearL d y
      ∃ F F1 : ℝ → SmoothCoefficientMatrix 2,∃ C : SphereSobolev 1 →L[ℝ] SphereSobolev 0,
        (∀ θ z,z ∈ Metric.closedBall (0:X) 2 → coefficientMatrixField 2 (F θ) z = coordinateRotationPrincipalFamily i j
          (fun v : ℝ × X => principalCoefficient (framedNormalMetric d.g₁ d.frame d.expMap y r) v.2) ((θ,0),z)) ∧
        (∀ θ z,z ∈ Metric.closedBall (0:X) 2 → coefficientMatrixField 2 (F1 θ) z = ell (coordinateRotation i j θ z) • (1:Mat)) ∧
        (∀ θ,(strongDirichletOperator fixedSobolevCalculus 0 (F θ)).IsInvertible) ∧
        ContDiff ℝ ∞ (fun θ => actualHighRadialErrorL (F θ)-r • highFirstRadialVariationL F0 (F1 θ) c) ∧
        ‖C‖ ≤ CM*r^2 ∧ C.comp (sphereSobolevInclusionL (3/2:ℝ) 1 (by norm_num)) =
          (sphereSobolevInclusionL (1/2:ℝ) 0 (by norm_num)).comp
            (deriv (fun θ => actualHighRadialErrorL (F θ)-r • highFirstRadialVariationL F0 (F1 θ) c) 0) := by
  have hHTheorem := uniform_actual_high_radial_rotation_taylor hY hΩ hm K ρ c₀ M Cj hK hρ
  obtain ⟨ηH,CH,F0,hηH,hCH,hF0,hHData⟩ := hHTheorem
  have hLTheorem := uniform_actual_low_radial_rotation_taylor hY hΩ hm K ρ c₀ M Cj hK hρ
  obtain ⟨ηL,CL,hηL,hCL,hLData⟩ := hLTheorem
  have hETheorem := uniform_enlarged_framed_normal_elliptic (Y:=Y) hΩ (by omega) K ρ c₀ M Cj hK hρ 2 (by norm_num)
  obtain ⟨ηE,hηE,hEData⟩ := hETheorem
  refine ⟨min ηH (min ηL ηE),(CL+CH)/2,F0,lt_min hηH (lt_min hηL hηE),by positivity,hF0,?_⟩
  intro floor hf ε hε hSmall d hd y hy i j
  dsimp only
  let c := firstMetricDensityFactor d.γ d.g₁ y
  let r := d.radius y
  let ell := firstDensityCenterLinearL d y
  let H := framedNormalMetric d.g₁ d.frame d.expMap y r
  let KP := 4*K^2
  have hSH := hSmall.trans (min_le_left _ _)
  have hSL := hSmall.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hSE := hSmall.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hHPoint := hHData floor hf ε hε hSH d hd y hy i j
  obtain ⟨F,F1,hRepH,hRepH1,hInvH,hSmoothH,hDH⟩ := hHPoint
  have hLPoint := hLData floor hf ε hε hSL d hd y hy i j
  obtain ⟨a,ha,S,hS,hz,a1,ha1,S1,hS1,hz1,hRepL,hRepL1,hDiffL,hDL⟩ := hLPoint
  have hc : 0 < c := firstMetricDensityFactor_pos _ _ _
  have hKP : 1 ≤ KP := by dsimp [KP];nlinarith [sq_nonneg (K-1)]
  have hEH : Elliptic (Metric.closedBall (0:X) 2) KP H := hEData floor hf ε hε hSE d hd y hy d.g₁ (by simp)
  let L := fun θ => commonSupportLowRadialErrorL a ha S hS hz θ-r • commonSupportLowFirstRadialL a1 ha1 S1 hS1 hz1 c θ
  let Hcurve := fun θ => actualHighRadialErrorL (F θ)-r • highFirstRadialVariationL F0 (F1 θ) c
  have hCompatible (θ : ℝ) : (sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)).comp (Hcurve θ) =
      (L θ).comp (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)) :=
    rotated_radial_taylor_endpoints_compatible H KP hKP hEH i j a a1 ha ha1 S S1 hS hS1 hz hz1 θ c r ell hc F0 (F θ) (F1 θ)
      (fun z hzB => hF0 z (unitBall_subset_closedBall_two hzB))
      (hRepL θ) (hRepL1 θ) (hRepH θ) (hRepH1 θ) (hInvH θ)
  have hCompatibleM (θ : ℝ) : (sphereSobolevInclusionL (1/2:ℝ) (-1/2:ℝ) (by norm_num)).comp (Hcurve θ) =
      (L θ).comp (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)) := by
    have hI := sphereSobolevInclusionL_eq_of_target_eq (1/2:ℝ) (-1/2:ℝ) (-(1/2:ℝ))
      (by norm_num) (by norm_num) (by ring)
    exact (congrArg (fun I : SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ)) =>
      I.comp (Hcurve θ)) hI).trans (hCompatible θ)
  have hDiffH := hSmoothH.differentiable (by simp) 0
  have hMidpointTheorem := exists_midpoint_of_compatible_endpoint_derivatives L Hcurve hDiffL hDiffH
    (Filter.Eventually.of_forall hCompatibleM) CL CH r hDL hDH
  obtain ⟨C,hNC,hRestriction⟩ := hMidpointTheorem
  exact ⟨F,F1,C,hRepH,hRepH1,hInvH,hSmoothH,hNC,hRestriction⟩

end ShrinkingSpheres
