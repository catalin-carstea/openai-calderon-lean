import Proof.UniformRadialRotationFamilyDerivative
import Proof.RadialRotationCommutator
import Proof.ActualLocalRotatedRadialFamily
import Proof.QuadraticMidpointRadial

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3500000
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

/-- The actual quadratic radial remainder and each of its angular
    commutators are uniformly bounded H1-to-L2 maps of order radius squared.
    The commutator is identified as an equality of distributions on H2 data. -/
theorem uniform_actual_radial_angular_commutator {Y Ω : Set X}
    (hY : IsOpen Y) (hΩ : IsOpen Ω) {m : ℕ} (hm : 4 ≤ m)
    (K ρ c₀ : ℝ) (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ) (hK : 1 ≤ K) (hρ : 0 < ρ) :
    ∃ η CJ CC : ℝ,0 < η ∧ 0 ≤ CJ ∧ 0 ≤ CC ∧
      ∀ floor,1 ≤ floor → ∀ ε,0 ≤ ε → ε ≤ η → ∀ d,
      Admissible Y Ω K ρ c₀ M Cj floor ε d → ∀ y ∈ Y,∀ i j : I,
      ∃ R C : SphereSobolev 1 →L[ℝ] SphereSobolev 0,
        RealizesActualMidpointRadialError d y R ∧
        ‖R-d.radius y • (firstRadialCorrectionL d y).comp (sphereSobolevInclusionL 1 0 (by norm_num))‖ ≤ CJ*(d.radius y)^2 ∧
        ‖C‖ ≤ CC*(d.radius y)^2 ∧ ∀ f : SphereSobolev 2,
        let P := R-d.radius y • (firstRadialCorrectionL d y).comp (sphereSobolevInclusionL 1 0 (by norm_num))
        sphereSobolevRotationL 0 i j (P (sphereSobolevInclusionL 2 1 (by norm_num) f)) =
          sphereSobolevInclusionL 0 (-1) (by norm_num)
            (C (sphereSobolevInclusionL 2 1 (by norm_num) f)+P (sphereSobolevRotationL 2 i j f)) := by
  have hDerivativeTheorem := uniform_actual_radial_rotation_family_derivative hY hΩ hm K ρ c₀ M Cj hK hρ
  obtain ⟨ηD,CC,hηD,hCC,hDerivative⟩ := hDerivativeTheorem
  have hRawTheorem := uniform_actual_normal_local_rotated_radial_family hY hΩ (by omega) K ρ c₀ M Cj hK hρ
  obtain ⟨ηR,hηR,hRaw⟩ := hRawTheorem
  have hPointTheorem := uniform_actual_midpoint_radial_taylor_canonical (Y:=Y) hΩ (by omega) K ρ c₀ M Cj hK hρ
  obtain ⟨ηP,CB,CJ,hηP,hCB,hCJ,hPoint⟩ := hPointTheorem
  refine ⟨min ηD (min ηR ηP),CJ,CC,lt_min hηD (lt_min hηR hηP),hCJ,hCC,?_⟩
  intro floor hf ε hε hSmall d hd y hy i j
  have hSD := hSmall.trans (min_le_left _ _)
  have hSR := hSmall.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hSP := hSmall.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hRawHere := hRaw floor hf ε hε hSR d hd y hy
  obtain ⟨A,hA,L,hL,hz,V,hV,hyV,hVY,hRep,hFamilies⟩ := hRawHere
  obtain ⟨RR,hSmooth,hRestrict,hActual,hCov⟩ := hFamilies i j
  let R := fun θ => RR (θ,y)
  let G := fun θ => rotatedCommonSupportMatrixFamily i j A hA L hz (θ,y)
  let c := firstMetricDensityFactor d.γ d.g₁ y
  let ell := firstDensityCenterLinearL d y
  let r := d.radius y
  let B0 := firstRadialCorrectionL d y
  let B1 := radialCorrectionSobolevL 1 (c⁻¹ • ell)
  let D := radialCorrectionCovectorL (rotationCovector (c⁻¹ • ell) i j)
  let P := fun θ => R θ-r • (coarseFirstRadialVariationL c
    (ell.comp (coordinateRotationIsometry i j θ).toContinuousLinearEquiv.toContinuousLinearMap)).comp
      (sphereSobolevInclusionL 1 0 (by norm_num))
  have hDiffR : DifferentiableAt ℝ R 0 := by
    have hAt : ContDiffAt ℝ ∞ RR (0,y) :=
      hSmooth.contDiffAt ((isOpen_univ.prod hV).mem_nhds ⟨mem_univ _,hyV⟩)
    exact (hAt.comp 0 (contDiffAt_id.prodMk contDiffAt_const)).differentiableAt (by simp)
  have hG (θ : ℝ) (z : X) (hzB : z ∈ (ballOpens:Set X)) : coefficientMatrixField 2 (G θ) z =
      coordinateRotationPrincipalFamily i j
        (fun v : ℝ × X => principalCoefficient (framedNormalMetric d.g₁ d.frame d.expMap y r) v.2) ((θ,0),z) := by
    have hRot : coordinateRotation i j θ z ∈ Metric.closedBall (0:X) 2 := by
      simpa only [Metric.mem_closedBall,dist_zero_right,coordinateRotation_norm] using
        (unitBall_subset_closedBall_two hzB)
    rw [coefficientMatrixField_rotatedCommonSupportMatrixFamily]
    dsimp only [coordinateRotationPrincipalFamily]
    rw [(hRep y hyV _ hRot).eq_of_nhds]
  have hDerivativeHere := hDerivative floor hf ε hε hSD d hd y hy i j R G hDiffR hG
    (fun θ => hRestrict (θ,y) ⟨mem_univ _,hyV⟩)
  have hDP : DifferentiableAt ℝ P 0 := hDerivativeHere.1
  have hND : ‖deriv P 0‖ ≤ CC*r^2 := hDerivativeHere.2
  have hCovR (θ : ℝ) (u : SphereSobolev 1) :
      R θ (sphereSobolevOrthogonalPullbackL 1 (coordinateRotationIsometry i j θ) u) =
        sphereSobolevOrthogonalPullbackL 0 (coordinateRotationIsometry i j θ) (R 0 u) := by
    exact congrArg (fun T => T u) (hCov θ y hyV)
  let Pre : (SphereSobolev 0 →L[ℝ] SphereSobolev 0) →L[ℝ]
      (SphereSobolev 1 →L[ℝ] SphereSobolev 0) :=
    (ContinuousLinearMap.compL ℝ (SphereSobolev 1) (SphereSobolev 0) (SphereSobolev 0)).flip
      (sphereSobolevInclusionL 1 0 (by norm_num))
  have hPre := Pre.hasFDerivAt.comp_hasDerivAt (0:ℝ) (hasDerivAt_firstRadial_rotation_zero c ell i j)
  have hDC : deriv P 0 = deriv R 0-r • D.comp (sphereSobolevInclusionL 1 0 (by norm_num)) :=
    (hDiffR.hasDerivAt.sub (hPre.const_smul r)).deriv
  have hCompat (v : SphereSobolev 1) : sphereSobolevInclusionL 1 0 (by norm_num) (B1 v) =
      B0 (sphereSobolevInclusionL 1 0 (by norm_num) v) := by
    dsimp only [B0,firstRadialCorrectionL,c,ell]
    rw [coarseFirstRadialVariationL_normalized_covector]
    exact radialCorrectionSobolevL_coarse _ v
  have hComm : (sphereSobolevRotationL 1 i j).comp B1-B0.comp (sphereSobolevRotationL 1 i j) =
      D.comp (sphereSobolevInclusionL 1 0 (by norm_num)) := by
    dsimp only [B0,firstRadialCorrectionL,c,ell]
    rw [coarseFirstRadialVariationL_normalized_covector]
    exact rotation_radialCorrection_commutator i j _
  have hPointHere := hPoint floor hf ε hε hSP d hd y hy
  obtain ⟨FP,J,hRepP,hInvP,hBN,hJN,hJR⟩ := hPointHere
  have hFP (z : X) (hzB : z ∈ (ballOpens:Set X)) : coefficientMatrixField 2 FP z =
      principalCoefficient (framedNormalMetric d.g₁ d.frame d.expMap y r) z := by
    ext k l
    exact (hRepP z (unitBall_subset_closedBall_two hzB) k l).eq_of_nhds
  have hEqComp := (hActual y hyV FP hFP).trans hJR.symm
  have hZero : R 0 = J+r • B0.comp (sphereSobolevInclusionL 1 0 (by norm_num)) := by
    apply DFunLike.ext'
    exact (denseRange_sphereSobolevInclusionL (3/2:ℝ) 1 (by norm_num)).equalizer
      (R 0).continuous (J+r • B0.comp (sphereSobolevInclusionL 1 0 (by norm_num))).continuous
      (funext fun f => congrArg (fun T => T f) hEqComp)
  refine ⟨R 0,deriv P 0,hActual y hyV,?_,hND,?_⟩
  · change ‖R 0-r • B0.comp (sphereSobolevInclusionL 1 0 (by norm_num))‖ ≤ CJ*r^2
    rw [hZero,add_sub_cancel_right]
    exact hJN
  · intro f
    exact radial_taylor_rotation_commutator_distribution i j r R (deriv R 0) (deriv P 0)
      B0 D B1 hDiffR.hasDerivAt hCovR hCompat hComm hDC f

end ShrinkingSpheres
