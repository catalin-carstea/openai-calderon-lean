import Proof.ConormalTaylorCompatibility
import Proof.CoarseConormalSymmetry

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3600000
set_option maxSynthPendingDepth 15
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter MeasureTheory
open scoped ENNReal Topology InnerProductSpace
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.EnergyBridge OAI.AnisotropicCalderon.DirichletFamily
open OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open OAI.AnisotropicCalderon.SphereHarmonic OAI.AnisotropicCalderon.SpectralCoreRegularity
open OAI.AnisotropicCalderon.NativePolynomialBulkMoments
open OAI.AnisotropicCalderon.NativeSmoothSharpTraceCompletion
attribute [local irreducible] nativeWeakHalfLift nativeCoefficientWeakFunctionalInverse
  nativeWeakConormalEndpoint weakFirstConormalVariationL actualHighConormalL highConormalFlatL
  highFirstConormalVariationL strongPoissonL strongFirstPoissonVariationL

/-- The actual conormal first Taylor remainder has a common quadratic H1-to-L2
    bound and retains symmetry in the physical L2 pairing. The same compact
    coefficient witnesses appear in its high and weak endpoint identities. -/
theorem uniform_actual_midpoint_conormal_taylor {Y Ω : Set X} (hΩ : IsOpen Ω)
    {m : ℕ} (hm : 3 ≤ m) (K ρ c₀ : ℝ) (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ)
    (hK : 1 ≤ K) (hρ : 0 < ρ) :
    ∃ η CJ : ℝ,∃ F0 : SmoothCoefficientMatrix 2,0 < η ∧ 0 ≤ CJ ∧
      (∀ x ∈ Metric.closedBall (0:X) 2,coefficientMatrixField 2 F0 x = 1) ∧
      ∀ floor,1 ≤ floor → ∀ ε,0 ≤ ε → ε ≤ η → ∀ d,
      Admissible Y Ω K ρ c₀ M Cj floor ε d → ∀ y ∈ Y,
      let a := principalCoefficient (framedNormalMetric d.g₁ d.frame d.expMap y (d.radius y))
      let KP := 4*K^2
      let c := firstMetricDensityFactor d.γ d.g₁ y
      let ell := firstDensityCenterLinearL d y
      ∃ F F1 : SmoothCoefficientMatrix 2,
      ∃ e : NativeWeakEnergyData a (5*metricDensityBudget KP*KP) (metricDensityBudget KP*KP),
      ∃ ha1 : MemLp (fun x => TauCeti.PDE.energyIntegrand (coefficientMatrixField 2 F1 x) 0 0) ⊤
        ((volume:Measure X).restrict ballOpens),
      ∃ R : SphereSobolev 1 →L[ℝ] SphereSobolev 0,
        (∀ x ∈ Metric.closedBall (0:X) 2,∀ i j,coefficientValue 2 (F i j) =ᶠ[𝓝 x] (fun z => a z i j)) ∧
        (∀ x ∈ Metric.closedBall (0:X) 2,∀ i j,coefficientValue 2 (F1 i j) =ᶠ[𝓝 x] (fun z => ell z*(1:Mat) i j)) ∧
        (strongDirichletOperator fixedSobolevCalculus 0 F).IsInvertible ∧
        (strongDirichletOperator fixedSobolevCalculus 0 (c • F0)).IsInvertible ∧
        ‖R‖ ≤ CJ*(d.radius y)^2 ∧
        R.comp (sphereSobolevInclusionL (3/2:ℝ) 1 (by norm_num)) =
          (sphereSobolevInclusionL (1/2:ℝ) 0 (by norm_num)).comp
            (actualHighConormalL F-highConormalFlatL c-d.radius y • highFirstConormalVariationL F0 F1 c) ∧
        (sphereSobolevInclusionL 0 (-(1/2:ℝ)) (by norm_num)).comp R =
          (nativeWeakConormalEndpoint a 0 0 e.coefficient_bound sphereFischerInner-c • fixedLowRadialL-
            d.radius y • weakFirstConormalVariationL c (coefficientMatrixField 2 F1) ha1).comp
              (sphereSobolevInclusionL 1 (1/2:ℝ) (by norm_num)) ∧
        ∀ u v,⟪R u,sphereSobolevInclusionL 1 0 (by norm_num) v⟫_ℝ =
          ⟪sphereSobolevInclusionL 1 0 (by norm_num) u,R v⟫_ℝ := by
  obtain ⟨ηW,P,Q,CP1,CP2,F0W,hηW,hP,hQ,hCP1,hCP2,hF0W,hWeak⟩ :=
    uniform_actual_weak_poisson_taylor (Y:=Y) hΩ hm K ρ c₀ M Cj hK hρ
  obtain ⟨ηH,CH,F0,hηH,hCH,hF0,hHigh⟩ :=
    uniform_actual_high_conormal_taylor (Y:=Y) hΩ hm K ρ c₀ M Cj hK hρ
  obtain ⟨ηE,hηE,hElliptic⟩ := uniform_enlarged_framed_normal_elliptic
    (Y:=Y) hΩ (by omega) K ρ c₀ M Cj hK hρ 2 (by norm_num)
  let KP := 4*K^2
  let DA := metricDensityBudget KP*KP
  let CL := sphereSurfaceMass⁻¹*((DA*CP2+(9*P+9*Q)*CP1+9*Q*‖fixedHarmonicH1LiftL‖)*‖fixedHarmonicH1LiftL‖)
  have hDA : 0 ≤ DA := by dsimp [DA,KP,metricDensityBudget];positivity
  have hCL : 0 ≤ CL := by
    change 0 ≤ sphereSurfaceMass⁻¹*((DA*CP2+(9*P+9*Q)*CP1+9*Q*‖fixedHarmonicH1LiftL‖)*‖fixedHarmonicH1LiftL‖)
    exact mul_nonneg (inv_nonneg.mpr sphereSurfaceMass_pos.le) (by positivity)
  refine ⟨min (min ηW ηH) ηE,(CL+CH)/2,F0,lt_min (lt_min hηW hηH) hηE,by positivity,hF0,?_⟩
  intro floor hf ε hε hSmall d hd y hy
  dsimp only
  obtain ⟨FW,F1W,hRepW,hRep1W,hInvW,hInv0W,hValW,hDerivW,hValRW,hDerivRW,tW⟩ :=
    hWeak floor hf ε hε (hSmall.trans ((min_le_left _ _).trans (min_le_left _ _))) d hd y hy
  have hHighHere := hHigh floor hf ε hε (hSmall.trans ((min_le_left _ _).trans (min_le_right _ _))) d hd y hy
  dsimp only at hHighHere
  obtain ⟨F,F1,ha1,hRep,hRep1,hInv,hInv0,hHighNorm⟩ := hHighHere
  let a := principalCoefficient (framedNormalMetric d.g₁ d.frame d.expMap y (d.radius y))
  let c := firstMetricDensityFactor d.γ d.g₁ y
  let ell := firstDensityCenterLinearL d y
  let r := d.radius y
  have hr : 0 < r := (hd.2.2.2.2.1.2 y hy).1
  have hc : 0 < c := firstMetricDensityFactor_pos _ _ _
  have hPoint (x : X) (hx : x ∈ (ballOpens:Set X)) : coefficientMatrixField 2 F x = a x := by
    ext i j
    exact (hRep x (unitBall_subset_closedBall_two hx) i j).eq_of_nhds
  have hFirstEq := weakFirstConormal_congr_on_ball c tW.first_coefficient_bound ha1 (by
    intro x hx
    ext i j
    exact (hRep1W x (unitBall_subset_closedBall_two hx) i j).eq_of_nhds.trans
      (hRep1 x (unitBall_subset_closedBall_two hx) i j).eq_of_nhds.symm)
  let T0 := nativeWeakConormalEndpoint a 0 0 tW.energy.coefficient_bound sphereFischerInner-c • fixedLowRadialL-
    r • weakFirstConormalVariationL c (coefficientMatrixField 2 F1) ha1
  let T1 := actualHighConormalL F-highConormalFlatL c-r • highFirstConormalVariationL F0 F1 c
  have hLowNorm : ‖T0‖ ≤ CL*r^2 := by
    have hb := tW.conormal_remainder_bound hr.le hDA hP hQ hCP1 hCP2
    have hEq := congrArg (fun N : SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ)) =>
      nativeWeakConormalEndpoint a 0 0 tW.energy.coefficient_bound sphereFischerInner-c • fixedLowRadialL-r • N) hFirstEq
    have hn := congrArg (fun N : SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ)) => ‖N‖) hEq
    exact hn.symm.le.trans hb
  have hCompat := conormalTaylor_endpoints_compatible tW.energy.coefficient_bound tW.energy.coercive
    F F0 F1 c r hc hPoint (fun x hx => hF0 x (unitBall_subset_closedBall_two hx)) ha1 hInv hInv0
  have hCompatM : (sphereSobolevInclusionL (1/2:ℝ) (-1/2:ℝ) (by norm_num)).comp T1 =
      T0.comp (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)) := by
    have hI := sphereSobolevInclusionL_eq_of_target_eq (1/2:ℝ) (-1/2:ℝ) (-(1/2:ℝ))
      (by norm_num) (by norm_num) (by ring)
    exact (congrArg (fun I : SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ)) => I.comp T1) hI).trans hCompat
  let R := sphereSobolevMidpointL T0 T1 hCompatM
  have hRN : ‖R‖ ≤ ((CL+CH)/2)*r^2 :=
    (norm_sphereSobolevMidpointL_le T0 T1 hCompatM).trans (by
      have hSum := add_le_add hLowNorm hHighNorm
      nlinarith only [hSum])
  have hLower : (sphereSobolevInclusionL 0 (-(1/2:ℝ)) (by norm_num)).comp R =
      T0.comp (sphereSobolevInclusionL 1 (1/2:ℝ) (by norm_num)) := by
    have hI := sphereSobolevInclusionL_eq_of_target_eq 0 (-(1/2:ℝ)) (-1/2:ℝ)
      (by norm_num) (by norm_num) (by ring)
    exact (congrArg (fun I : SphereSobolev 0 →L[ℝ] SphereSobolev (-(1/2:ℝ)) => I.comp R) hI).trans
      (sphereSobolevInclusionL_midpoint T0 T1 hCompatM)
  have hEll := hElliptic floor hf ε hε (hSmall.trans (min_le_right _ _)) d hd y hy d.g₁ (by simp)
  have hs : ∀ᵐ x ∂((volume:Measure X).restrict ballOpens),(a x).IsSymm := by
    filter_upwards [ae_restrict_mem ballOpens.isOpen.measurableSet] with x hx
    change (OAI.AnisotropicCalderon.vol _ x •
      ((framedNormalMetric d.g₁ d.frame d.expMap y r) x)⁻¹).IsSymm
    have hSymmetric : ((framedNormalMetric d.g₁ d.frame d.expMap y r) x).IsSymm :=
      (hEll.2 x (unitBall_subset_closedBall_two hx)).1
    exact hSymmetric.inv.smul _
  have hs1 : ∀ᵐ x ∂((volume:Measure X).restrict ballOpens),(coefficientMatrixField 2 F1 x).IsSymm := by
    filter_upwards [ae_restrict_mem ballOpens.isOpen.measurableSet] with x hx
    have hMat : coefficientMatrixField 2 F1 x = ell x • (1:Mat) := by
      ext i j
      exact (hRep1 x (unitBall_subset_closedBall_two hx) i j).eq_of_nhds
    rw [hMat]
    exact Matrix.isSymm_one.smul _
  refine ⟨F,F1,tW.energy,ha1,R,hRep,hRep1,hInv,hInv0,hRN,
    sphereSobolevMidpointL_inclusion T0 T1 hCompatM,hLower,?_⟩
  exact conormal_midpoint_symmetric T0 R hLower
    (nativeConormalTaylor_remainder_symmetric tW.energy.coefficient_bound ha1 tW.energy.coercive hs hs1 c r)

end ShrinkingSpheres
