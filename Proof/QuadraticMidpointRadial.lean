import Proof.CanonicalFirstRadialCorrection
import Proof.RadialTaylorCompatibility
import Proof.FirstRadialOrderZero
import Proof.ActualMidpointRadialEndpoint

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxSynthPendingDepth 15
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter MeasureTheory
open scoped ENNReal Topology
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.EnergyBridge OAI.AnisotropicCalderon.DirichletFamily
open OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open OAI.AnisotropicCalderon.SphereHarmonic OAI.AnisotropicCalderon.SpectralCoreRegularity

/-- The first radial variation depends only on its scalar affine coefficient,
    not on the compact representatives used for the strong inverse. -/
theorem highFirstRadialVariation_congr_scalar (F0 F1 G0 G1 : SmoothCoefficientMatrix 2)
    (c : ℝ) (hc : c ≠ 0) (ell : X →L[ℝ] ℝ)
    (hF0 : ∀ x ∈ (ballOpens:Set X),coefficientMatrixField 2 F0 x = 1)
    (hF1 : ∀ x ∈ (ballOpens:Set X),∀ i j,coefficientValue 2 (F1 i j) x = ell x*(1:Mat) i j)
    (hG0 : ∀ x ∈ (ballOpens:Set X),coefficientMatrixField 2 G0 x = 1)
    (hG1 : ∀ x ∈ (ballOpens:Set X),∀ i j,coefficientValue 2 (G1 i j) x = ell x*(1:Mat) i j)
    (hIF : (strongDirichletOperator fixedSobolevCalculus 0 (c • F0)).IsInvertible)
    (hIG : (strongDirichletOperator fixedSobolevCalculus 0 (c • G0)).IsInvertible) :
    highFirstRadialVariationL F0 F1 c = highFirstRadialVariationL G0 G1 c := by
  have hF := highFirstRadialVariation_coarse_eq F0 F1 c hc ell hF0 hF1 hIF
  have hG := highFirstRadialVariation_coarse_eq G0 G1 c hc ell hG0 hG1 hIG
  apply ContinuousLinearMap.ext
  intro f
  apply sphereSobolevInclusionL_injective (1/2:ℝ) 0 (by norm_num)
  exact congrArg (fun T : SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev 0 => T f) (hF.trans hG.symm)

/-- A common quadratic H1-to-L2 radial remainder after a uniformly bounded
    order-zero first correction, for every admitted first metric and radius. -/
theorem uniform_actual_midpoint_radial_taylor_canonical {Y Ω : Set X} (hΩ : IsOpen Ω)
    {m : ℕ} (hm : 3 ≤ m) (K ρ c₀ : ℝ) (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ)
    (hK : 1 ≤ K) (hρ : 0 < ρ) :
    ∃ η CB CJ : ℝ,0 < η ∧ 0 ≤ CB ∧ 0 ≤ CJ ∧ ∀ floor,1 ≤ floor → ∀ ε,0 ≤ ε → ε ≤ η → ∀ d,
      Admissible Y Ω K ρ c₀ M Cj floor ε d → ∀ y ∈ Y,
      let B := firstRadialCorrectionL d y
      ∃ F : SmoothCoefficientMatrix 2,∃ J : SphereSobolev 1 →L[ℝ] SphereSobolev 0,
        (∀ x ∈ Metric.closedBall (0:X) 2,∀ i j,coefficientValue 2 (F i j) =ᶠ[𝓝 x]
          (fun z => principalCoefficient (framedNormalMetric d.g₁ d.frame d.expMap y (d.radius y)) z i j)) ∧
        (strongDirichletOperator fixedSobolevCalculus 0 F).IsInvertible ∧
        ‖B‖ ≤ CB ∧ ‖J‖ ≤ CJ*(d.radius y)^2 ∧
        (J+d.radius y • B.comp (sphereSobolevInclusionL 1 0 (by norm_num))).comp
          (sphereSobolevInclusionL (3/2:ℝ) 1 (by norm_num)) =
          (sphereSobolevInclusionL (1/2:ℝ) 0 (by norm_num)).comp (actualHighRadialErrorL F) := by
  obtain ⟨ηL,CBL,CL,hηL,hCBL,hCL,hLow⟩ := uniform_actual_low_radial_taylor
    (Y:=Y) hΩ hm K ρ c₀ M Cj hK hρ
  obtain ⟨ηH,CH1,CH,F0H,hηH,hCH1,hCH,hF0H,hHigh⟩ := uniform_actual_high_radial_taylor
    (Y:=Y) hΩ hm K ρ c₀ M Cj hK hρ
  let PG := K^3*|M ⟨1,by omega⟩|
  have hKpos : 0 < K := zero_lt_one.trans_le hK
  have hPG : 0 ≤ PG := by dsimp [PG];positivity
  refine ⟨min ηL ηH,6*K*PG,(CL+CH)/2,lt_min hηL hηH,by positivity,by positivity,?_⟩
  intro floor hf ε hε hSmall d hd y hy
  obtain ⟨F0,F,F1,e,ha1,hF0,hRep,hRep1,hInv,hInv0,hNormal,hFirstLow,hLowNorm⟩ :=
    hLow floor hf ε hε (hSmall.trans (min_le_left _ _)) d hd y hy
  obtain ⟨FH,F1H,hRepH,hRepH1,hInvH,hInvH0,hFirstHigh,hHighNorm⟩ :=
    hHigh floor hf ε hε (hSmall.trans (min_le_right _ _)) d hd y hy
  let a := principalCoefficient (framedNormalMetric d.g₁ d.frame d.expMap y (d.radius y))
  let c := firstMetricDensityFactor d.γ d.g₁ y
  let ell := firstDensityCenterLinearL d y
  let r := d.radius y
  have hc : 0 < c := firstMetricDensityFactor_pos _ _ _
  have hPoint (x : X) (hx : x ∈ (ballOpens:Set X)) : coefficientMatrixField 2 F x = a x := by
    ext i j
    exact (hRep x (unitBall_subset_closedBall_two hx) i j).eq_of_nhds
  have hFG (x : X) (hx : x ∈ (ballOpens:Set X)) : coefficientMatrixField 2 F x = coefficientMatrixField 2 FH x := by
    ext i j
    exact (hRep x (unitBall_subset_closedBall_two hx) i j).eq_of_nhds.trans
      (hRepH x (unitBall_subset_closedBall_two hx) i j).eq_of_nhds.symm
  have hPoisson := strongPoissonL_congr_on_ball F FH hFG
  have hHighEq : actualHighRadialErrorL F = actualHighRadialErrorL FH :=
    congrArg (fun P : SphereSobolev (3/2:ℝ) →L[ℝ] BallSobolev 2 =>
      fixedHalfOutwardTraceL.comp P-fixedHalfOutwardTraceL.comp fixedHarmonicLiftL) hPoisson
  have hFirstEq := highFirstRadialVariation_congr_scalar F0 F1 F0H F1H c hc.ne' ell
    (fun x hx => hF0 x (unitBall_subset_closedBall_two hx))
    (fun x hx i j => (hRep1 x (unitBall_subset_closedBall_two hx) i j).eq_of_nhds)
    (fun x hx => hF0H x (unitBall_subset_closedBall_two hx))
    (fun x hx i j => (hRepH1 x (unitBall_subset_closedBall_two hx) i j).eq_of_nhds) hInv0 hInvH0
  have hHighF : ‖actualHighRadialErrorL F-r • highFirstRadialVariationL F0 F1 c‖ ≤ CH*r^2 := by
    have hEq := congrArg₂ (fun A B : SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ) => A-r • B)
      hHighEq hFirstEq
    have hn := congrArg (fun T : SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ) => ‖T‖) hEq
    exact hn.le.trans hHighNorm
  have hScalar (w : UnitSphere) : coefficientMatrixField 2 F1 w.val = ell w.val • (1:Mat) := by
    have hw : w.val ∈ Metric.closedBall (0:X) 2 :=
      Metric.closedBall_subset_closedBall (by norm_num) (Metric.sphere_subset_closedBall w.property)
    ext i j
    exact (hRep1 w.val hw i j).eq_of_nhds
  let T0 := actualLowRadialErrorL a e.coefficient_bound F-r • lowFirstRadialVariationL c F1 ha1
  let T1 := actualHighRadialErrorL F-r • highFirstRadialVariationL F0 F1 c
  have hCompat : (sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)).comp T1 =
      T0.comp (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)) :=
    radial_taylor_endpoints_compatible e.coefficient_bound e.coercive F0 F F1 c r ell hc ha1 hPoint
      (fun x hx => hF0 x (unitBall_subset_closedBall_two hx)) hScalar hInv hInv0 hNormal
  have hCompatM : (sphereSobolevInclusionL (1/2:ℝ) (-1/2:ℝ) (by norm_num)).comp T1 =
      T0.comp (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)) := by
    have hI := sphereSobolevInclusionL_eq_of_target_eq (1/2:ℝ) (-1/2:ℝ) (-(1/2:ℝ))
      (by norm_num) (by norm_num) (by ring)
    exact (congrArg (fun I : SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ)) => I.comp T1) hI).trans hCompat
  let J := sphereSobolevMidpointL T0 T1 hCompatM
  let B := coarseFirstRadialVariationL c ell
  have hJN : ‖J‖ ≤ ((CL+CH)/2)*r^2 :=
    (norm_sphereSobolevMidpointL_le T0 T1 hCompatM).trans (by
      have hSum := add_le_add hLowNorm hHighF
      nlinarith only [hSum])
  have hCenter := hd.2.1.center_mem hy
  have hci : |c⁻¹| ≤ K := by
    rw [abs_of_pos (inv_pos.mpr hc)]
    exact hd.1.firstMetricDensityFactor_inverse_le hKpos hCenter
  have hEll : ‖ell‖ ≤ PG := by
    have hFrame := hd.1.2.2.2.2.2.2.2 y hCenter
    have hEn := hd.1.1.norm_frameVectorLinear_le hK hCenter d.frame hFrame
    have hD := (hd.1.firstMetricDensityFactor_jet_bounds hΩ hKpos (by omega) hCenter).1
    exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
      ((mul_le_mul hD hEn (norm_nonneg _) (by positivity)).trans_eq (by dsimp [PG];ring))
  have hBN : ‖B‖ ≤ 6*K*PG := (norm_coarseFirstRadialVariationL_le c ell).trans (by gcongr)
  have hCoarse := highFirstRadialVariation_coarse_eq F0 F1 c hc.ne' ell
    (fun x hx => hF0 x (unitBall_subset_closedBall_two hx))
    (fun x hx i j => (hRep1 x (unitBall_subset_closedBall_two hx) i j).eq_of_nhds) hInv0
  have hResidual : (sphereSobolevInclusionL (1/2:ℝ) 0 (by norm_num)).comp T1 =
      (sphereSobolevInclusionL (1/2:ℝ) 0 (by norm_num)).comp (actualHighRadialErrorL F)-
        r • B.comp (sphereSobolevInclusionL (3/2:ℝ) 0 (by norm_num)) := by
    dsimp only [T1]
    rw [ContinuousLinearMap.comp_sub,ContinuousLinearMap.comp_smul]
    exact congrArg (fun S : SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev 0 =>
      (sphereSobolevInclusionL (1/2:ℝ) 0 (by norm_num)).comp (actualHighRadialErrorL F)-r • S) hCoarse
  have hJ := (sphereSobolevMidpointL_inclusion T0 T1 hCompatM).trans hResidual
  have hB : (B.comp (sphereSobolevInclusionL 1 0 (by norm_num))).comp
      (sphereSobolevInclusionL (3/2:ℝ) 1 (by norm_num)) =
      B.comp (sphereSobolevInclusionL (3/2:ℝ) 0 (by norm_num)) := by
    apply ContinuousLinearMap.ext
    intro f
    exact congrArg B (congrArg (fun I : SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev 0 => I f)
      (sphereSobolevInclusionL_trans (3/2:ℝ) 1 0 (by norm_num) (by norm_num)))
  refine ⟨F,J,hRep,hInv,hBN,hJN,?_⟩
  have hSum := congrArg₂ (fun A C : SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev 0 => A+r • C) hJ hB
  simpa only [J,r,B,firstRadialCorrectionL,c,ell,ContinuousLinearMap.add_comp,ContinuousLinearMap.smul_comp] using
    hSum.trans (sub_add_cancel _ _)

/-- Compatibility interface retaining the original existential correction. -/
theorem uniform_actual_midpoint_radial_taylor {Y Ω : Set X} (hΩ : IsOpen Ω)
    {m : ℕ} (hm : 3 ≤ m) (K ρ c₀ : ℝ) (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ)
    (hK : 1 ≤ K) (hρ : 0 < ρ) :
    ∃ η CB CJ : ℝ,0 < η ∧ 0 ≤ CB ∧ 0 ≤ CJ ∧ ∀ floor,1 ≤ floor → ∀ ε,0 ≤ ε → ε ≤ η → ∀ d,
      Admissible Y Ω K ρ c₀ M Cj floor ε d → ∀ y ∈ Y,
      ∃ F : SmoothCoefficientMatrix 2,∃ B : SphereSobolev 0 →L[ℝ] SphereSobolev 0,
      ∃ J : SphereSobolev 1 →L[ℝ] SphereSobolev 0,
        (∀ x ∈ Metric.closedBall (0:X) 2,∀ i j,coefficientValue 2 (F i j) =ᶠ[𝓝 x]
          (fun z => principalCoefficient (framedNormalMetric d.g₁ d.frame d.expMap y (d.radius y)) z i j)) ∧
        (strongDirichletOperator fixedSobolevCalculus 0 F).IsInvertible ∧
        ‖B‖ ≤ CB ∧ ‖J‖ ≤ CJ*(d.radius y)^2 ∧
        (J+d.radius y • B.comp (sphereSobolevInclusionL 1 0 (by norm_num))).comp
          (sphereSobolevInclusionL (3/2:ℝ) 1 (by norm_num)) =
          (sphereSobolevInclusionL (1/2:ℝ) 0 (by norm_num)).comp (actualHighRadialErrorL F) := by
  obtain ⟨η,CB,CJ,hη,hCB,hCJ,hProduce⟩ :=
    uniform_actual_midpoint_radial_taylor_canonical (Y:=Y) hΩ hm K ρ c₀ M Cj hK hρ
  refine ⟨η,CB,CJ,hη,hCB,hCJ,?_⟩
  intro floor hf ε hε hSmall d hd y hy
  have hHere := hProduce floor hf ε hε hSmall d hd y hy
  dsimp only at hHere
  obtain ⟨F,J,hRep,hInv,hB,hJ,hRestriction⟩ := hHere
  exact ⟨F,firstRadialCorrectionL d y,J,hRep,hInv,hB,hJ,hRestriction⟩

end ShrinkingSpheres
