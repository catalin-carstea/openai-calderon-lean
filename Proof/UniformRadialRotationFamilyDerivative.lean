import Proof.MidpointRotationDerivative
import Proof.RadialRotationTaylorRestriction
import Proof.FirstRadialRotationDerivative
import Proof.UniformMidpointRadialRotationDerivative
import Proof.FlatCoefficientEllipticity

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2600000
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

/-- The uniform interpolated derivative bound belongs to every genuine
    differentiable midpoint family of the same actual rotated coefficients. -/
theorem uniform_actual_radial_rotation_family_derivative {Y Ω : Set X}
    (hY : IsOpen Y) (hΩ : IsOpen Ω) {m : ℕ} (hm : 4 ≤ m)
    (K ρ c₀ : ℝ) (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ) (hK : 1 ≤ K) (hρ : 0 < ρ) :
    ∃ η CM : ℝ,0 < η ∧ 0 ≤ CM ∧
      ∀ floor,1 ≤ floor → ∀ ε,0 ≤ ε → ε ≤ η → ∀ d,
      Admissible Y Ω K ρ c₀ M Cj floor ε d → ∀ y ∈ Y,∀ i j : I,
      ∀ (R : ℝ → SphereSobolev 1 →L[ℝ] SphereSobolev 0)
        (G : ℝ → SmoothCoefficientMatrix 2),
      DifferentiableAt ℝ R 0 →
      (∀ θ z,z ∈ (ballOpens:Set X) → coefficientMatrixField 2 (G θ) z = coordinateRotationPrincipalFamily i j
        (fun v : ℝ × X => principalCoefficient (framedNormalMetric d.g₁ d.frame d.expMap y (d.radius y)) v.2) ((θ,0),z)) →
      (∀ θ,(R θ).comp (sphereSobolevInclusionL (3/2:ℝ) 1 (by norm_num)) =
        (sphereSobolevInclusionL (1/2:ℝ) 0 (by norm_num)).comp (actualHighRadialErrorL (G θ))) →
      let c := firstMetricDensityFactor d.γ d.g₁ y
      let ell := firstDensityCenterLinearL d y
      let P := fun θ => R θ-d.radius y • (coarseFirstRadialVariationL c
        (ell.comp (coordinateRotationIsometry i j θ).toContinuousLinearEquiv.toContinuousLinearMap)).comp
          (sphereSobolevInclusionL 1 0 (by norm_num))
      DifferentiableAt ℝ P 0 ∧ ‖deriv P 0‖ ≤ CM*(d.radius y)^2 := by
  have hProducer := uniform_actual_midpoint_radial_rotation_derivative hY hΩ hm K ρ c₀ M Cj hK hρ
  obtain ⟨η,CM,F0,hη,hCM,hF0,hData⟩ := hProducer
  refine ⟨η,CM,hη,hCM,?_⟩
  intro floor hf ε hε hSmall d hd y hy i j R G hDiffR hRepG hR
  dsimp only
  let c := firstMetricDensityFactor d.γ d.g₁ y
  let ell := firstDensityCenterLinearL d y
  let q := fun θ => ell.comp (coordinateRotationIsometry i j θ).toContinuousLinearEquiv.toContinuousLinearMap
  let P := fun θ => R θ-d.radius y • (coarseFirstRadialVariationL c (q θ)).comp
    (sphereSobolevInclusionL 1 0 (by norm_num))
  have hHere := hData floor hf ε hε hSmall d hd y hy i j
  obtain ⟨F,F1,C,hRepF,hRepF1,hInvF,hSmoothH,hCN,hC⟩ := hHere
  let H := fun θ => actualHighRadialErrorL (F θ)-d.radius y • highFirstRadialVariationL F0 (F1 θ) c
  have hc : 0 < c := firstMetricDensityFactor_pos _ _ _
  have hFlat : ∀ z ∈ (ballOpens:Set X),coefficientMatrixField 2 F0 z = 1 :=
    fun z hz => hF0 z (unitBall_subset_closedBall_two hz)
  have hInv0 : (strongDirichletOperator fixedSobolevCalculus 0 (c • F0)).IsInvertible :=
    strongDirichletOperator_isInvertible_of_elliptic fixedSobolevCalculus fixedDirichletRegularity 0
      (c • F0) (uniformlyEllipticOn_flat_coefficientMatrix F0 c hc hFlat)
  have hB := hasDerivAt_firstRadial_rotation_zero c ell i j
  let Pre : (SphereSobolev 0 →L[ℝ] SphereSobolev 0) →L[ℝ]
      (SphereSobolev 1 →L[ℝ] SphereSobolev 0) :=
    (ContinuousLinearMap.compL ℝ (SphereSobolev 1) (SphereSobolev 0) (SphereSobolev 0)).flip
      (sphereSobolevInclusionL 1 0 (by norm_num))
  have hPre := Pre.hasFDerivAt.comp_hasDerivAt (0:ℝ) hB
  have hDP : DifferentiableAt ℝ P 0 := hDiffR.sub (hPre.differentiableAt.const_smul (d.radius y))
  have hCompatible (θ : ℝ) : (P θ).comp (sphereSobolevInclusionL (3/2:ℝ) 1 (by norm_num)) =
      (sphereSobolevInclusionL (1/2:ℝ) 0 (by norm_num)).comp (H θ) := by
    apply midpoint_radial_taylor_high_restriction (R θ) (G θ) (F θ) F0 (F1 θ) c (d.radius y) hc.ne' (q θ)
      (hR θ) (fun z hz => (hRepG θ z hz).trans (hRepF θ z (unitBall_subset_closedBall_two hz)).symm) hFlat
      (fun z hz k l => ?_) hInv0
    change coefficientMatrixField 2 (F1 θ) z k l = ell (coordinateRotation i j θ z)*(1:Mat) k l
    exact congrArg (fun A : Mat => A k l) (hRepF1 θ z (unitBall_subset_closedBall_two hz))
  have hEq := midpoint_curve_derivative_eq_of_high_restriction P H C hDP
    (hSmoothH.differentiable (by simp) 0) (Filter.Eventually.of_forall fun θ => (hCompatible θ).symm) hC
  exact ⟨hDP,hEq ▸ hCN⟩

end ShrinkingSpheres
