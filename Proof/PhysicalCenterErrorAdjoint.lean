import Proof.BoundaryGradientValues

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3200000
set_option maxSynthPendingDepth 15
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter MeasureTheory
open scoped ContDiff Topology ENNReal InnerProductSpace
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.EnergyBridge OAI.AnisotropicCalderon.DirichletFamily
open OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open OAI.AnisotropicCalderon.SphereHarmonic

/-- The center-error boundary gradient is genuinely the geometric gradient of
    the same physical harmonic solution. Its rescaled L2 adjoint is uniformly
    radius-linear; all radial and coefficient witnesses are shared. -/
theorem uniform_physical_center_error_gradient_adjoint_canonical {Y Ω : Set X} (hY : IsOpen Y) (hΩ : IsOpen Ω)
    {m : ℕ} (hm : 3 ≤ m) (K ρ c₀ : ℝ) (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ)
    (hK : 1 ≤ K) (hρ : 0 < ρ) :
    ∃ η CD CB CJ CE : ℝ,0 < η ∧ 0 ≤ CD ∧ 0 ≤ CB ∧ 0 ≤ CJ ∧ 0 ≤ CE ∧
      ∀ floor,1 ≤ floor → ∀ ε,0 ≤ ε → ε ≤ η → ∀ d,
      Admissible Y Ω K ρ c₀ M Cj floor ε d → ∀ y ∈ Y,
      ∃ Fp : SmoothCoefficientMatrix 2,
      ∃ D Da : SphereSobolev 1 →L[ℝ] SphereSobolev 0,∃ B : SphereSobolev 0 →L[ℝ] SphereSobolev 0,
        (∀ x ∈ Metric.closedBall (0:X) 2,∀ i j,coefficientValue 2 (Fp i j) =ᶠ[𝓝 x]
          (fun z => principalCoefficient (framedNormalMetric d.g₁ d.frame d.expMap y (d.radius y)) z i j)) ∧
        (strongDirichletOperator fixedSobolevCalculus 0 Fp).IsInvertible ∧
        ‖Da‖ ≤ CD ∧ B = firstRadialCorrectionL d y ∧ ‖B‖ ≤ CB ∧
        ‖Da-sphereSobolevDegreeL-d.radius y • B.adjoint.comp (sphereSobolevInclusionL 1 0 (by norm_num))‖ ≤ CJ*(d.radius y)^2 ∧
        (∀ u v,⟪D u,sphereSobolevInclusionL 1 0 (by norm_num) v⟫_ℝ =
          ⟪sphereSobolevInclusionL 1 0 (by norm_num) u,Da v⟫_ℝ) ∧
        (∀ f : SphereSobolev (3/2:ℝ),D (sphereSobolevInclusionL (3/2:ℝ) 1 (by norm_num) f) =
          sphereSobolevZeroEquiv orthogonalSphereHarmonics denseSphereHarmonics
            (outwardRadialTraceL fixedSobolevCalculus fixedUnitBallValueTrace (strongPoissonL Fp f))) ∧
        ∀ a : X,∃ C : I → SmoothCoefficientJets 2,
          (∀ j,∀ z ∈ Metric.closedBall (0:X) 1,coefficientValue 2 (C j) =ᶠ[𝓝 z]
            (fun w => metricPair d.γ y
              ((normalizedParallelCenterJacobian d.γ d.expMap y
                (d.radius y • frameVector d.frame y w)-ContinuousLinearMap.id ℝ X) a) (d.frame y j))) ∧
          ‖(d.radius y)⁻¹ • boundaryGradientAdjointL C Da‖ ≤ CE*‖a‖*d.radius y ∧
          ∀ u : X → ℝ,HarmonicOnBall d.g₁ (closedBallImage d.γ d.expMap d.radius y) u →
          ∀ f : SphereSobolev (3/2:ℝ),
          (fixedBoundaryValueL f =ᵐ[sphereProbability] fun w : UnitSphere =>
            u (normalChart d.expMap d.frame y (d.radius y) w.val)) →
          (sphereSobolevZeroEquiv orthogonalSphereHarmonics denseSphereHarmonics).symm
            (boundaryGradientL C D (sphereSobolevInclusionL (3/2:ℝ) 1 (by norm_num) f))
              =ᵐ[sphereProbability] fun w : UnitSphere =>
                fderiv ℝ (ballPullback d.expMap d.radius y u) (frameVector d.frame y w.val)
                  ((normalizedParallelCenterJacobian d.γ d.expMap y
                    (d.radius y • frameVector d.frame y w.val)-ContinuousLinearMap.id ℝ X) a) := by
  have hActualTheorem := uniform_actual_midpoint_radial_adjoint_canonical (Y:=Y) hΩ hm K ρ c₀ M Cj hK hρ
  obtain ⟨ηA,CB,CJ,hηA,hCB,hCJ,hActual⟩ := hActualTheorem
  have hPhysicalTheorem := uniform_physical_strong_poisson_realization (Y:=Y) hΩ hm K ρ c₀ M Cj hK hρ
  obtain ⟨ηP,hηP,hPhysical⟩ := hPhysicalTheorem
  have hCoefficientTheorem := uniform_center_error_vector_coefficients hY hΩ hm K ρ c₀ M Cj hK hρ
  obtain ⟨ηC,CG,hηC,hCG,hCoefficients⟩ := hCoefficientTheorem
  let CD := 2+CB+CJ
  let CE := (73*boundaryTangentialAdjointBudget+438*CD)*CG
  have hCD : 0 ≤ CD := by dsimp only [CD];positivity
  have hCE : 0 ≤ CE := by
    have := boundaryTangentialAdjointBudget_nonneg
    dsimp only [CE];positivity
  refine ⟨min ηA (min ηP (min ηC 1)),CD,CB,CJ,CE,
    lt_min hηA (lt_min hηP (lt_min hηC zero_lt_one)),hCD,hCB,hCJ,hCE,?_⟩
  intro floor hf ε hε hSmall d hd y hy
  have hAHere := hActual floor hf ε hε (hSmall.trans (min_le_left _ _)) d hd y hy
  dsimp only at hAHere
  obtain ⟨Fp,D,Da,hRep,hInv,hB,hTaylor,hPair,hD⟩ := hAHere
  let B := firstRadialCorrectionL d y
  have hr := (hd.2.2.2.2.1.2 y hy).1
  have hrε := (radius_bounds (d.radius y) (beta d.γ d.radius y) floor ε hr.le hf
    (hd.2.2.2.2.1.2 y hy).2.1 (hd.2.2.2.2.2 y hy).2).2.2
  have hr1 : d.radius y ≤ 1 := hrε.trans
    (hSmall.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))))
  have hDa : ‖Da‖ ≤ CD := norm_radial_adjoint_of_quadratic_taylor Da B (d.radius y) CB CJ hr.le hr1 hCB hCJ hB hTaylor
  refine ⟨Fp,D,Da,B,hRep,hInv,hDa,rfl,hB,hTaylor,hPair,hD,?_⟩
  intro a
  have hCHere := hCoefficients floor hf ε hε
    (hSmall.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))) d hd y hy a
  obtain ⟨C,hCRep,hCBound,hReconstruct⟩ := hCHere
  have hAdjoint := norm_boundaryGradientAdjointL_local_C1 C Da (CG*‖a‖*(d.radius y)^2) (by positivity) hCBound
  have hSmallAdjoint : ‖(d.radius y)⁻¹ • boundaryGradientAdjointL C Da‖ ≤ CE*‖a‖*d.radius y := by
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hr)]
    calc
      _ ≤ (d.radius y)⁻¹*((73*boundaryTangentialAdjointBudget+438*CD)*(CG*‖a‖*(d.radius y)^2)) := by
        gcongr
        exact hAdjoint.trans (by gcongr)
      _ = _ := by dsimp only [CE];field_simp <;> ring
  refine ⟨C,hCRep,hSmallAdjoint,?_⟩
  intro u hu f hBoundary
  have hPHere := hPhysical floor hf ε hε
    (hSmall.trans ((min_le_right _ _).trans (min_le_left _ _))) d hd y hy Fp hRep hInv u hu f hBoundary
  obtain ⟨U,hCompact,hNear,hIdent⟩ := hPHere
  let v := sphereSobolevInclusionL (3/2:ℝ) 1 (by norm_num) f
  have hInput : sphereSobolevInclusionL 1 (1/2:ℝ) (by norm_num) v =
      sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num) f :=
    congrArg (fun I : SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ) => I f)
      (sphereSobolevInclusionL_trans (3/2:ℝ) 1 (1/2:ℝ) (by norm_num) (by norm_num))
  have hValue := fixedHalfValueTrace_strongPoisson Fp f
  change OAI.AnisotropicCalderon.NativeFullSharpHalfTrace.nativeHalfTraceL
    sphereFischerInner orthogonalSphereHarmonics denseSphereHarmonics fixedUnitBallValueTrace
      (TauCeti.Wkp.firstOrder 1 (strongPoissonL Fp f)) = _ at hValue
  have hCoordinate (j : I) : strongCoordinateTraceL fixedSobolevCalculus fixedUnitBallValueTrace j (strongPoissonL Fp f)
      =ᵐ[sphereProbability] fun w : UnitSphere =>
        fderiv ℝ (u ∘ normalChart d.expMap d.frame y (d.radius y)) w.val (axis j) := by
    rw [← hIdent]
    exact strongCoordinateTrace_representative_ae U _ hNear j
  have hValues := boundaryGradientL_value_ae C D (strongPoissonL Fp f) v (hValue.trans hInput.symm) (hD f)
    (fun j w => fderiv ℝ (u ∘ normalChart d.expMap d.frame y (d.radius y)) w.val (axis j)) hCoordinate
  filter_upwards [hValues] with w hw
  have hClosed : w.val ∈ Metric.closedBall (0:X) 1 := by
    have hn : ‖w.val‖ = 1 := by simpa [UnitSphere,Metric.sphere,dist_eq_norm] using w.property
    simpa [Metric.mem_closedBall,dist_zero_right,hn]
  exact hw.trans (hd.center_error_gradient_eq hY hy u hu a w (fun j => coefficientValue 2 (C j) w.val)
    (hReconstruct w.val hClosed))


/-- The original existential interface, retained for existing callers. -/
theorem uniform_physical_center_error_gradient_adjoint {Y Ω : Set X} (hY : IsOpen Y) (hΩ : IsOpen Ω)
    {m : ℕ} (hm : 3 ≤ m) (K ρ c₀ : ℝ) (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ)
    (hK : 1 ≤ K) (hρ : 0 < ρ) :
    ∃ η CD CB CJ CE : ℝ,0 < η ∧ 0 ≤ CD ∧ 0 ≤ CB ∧ 0 ≤ CJ ∧ 0 ≤ CE ∧
      ∀ floor,1 ≤ floor → ∀ ε,0 ≤ ε → ε ≤ η → ∀ d,
      Admissible Y Ω K ρ c₀ M Cj floor ε d → ∀ y ∈ Y,
      ∃ Fp : SmoothCoefficientMatrix 2,
      ∃ D Da : SphereSobolev 1 →L[ℝ] SphereSobolev 0,∃ B : SphereSobolev 0 →L[ℝ] SphereSobolev 0,
        (∀ x ∈ Metric.closedBall (0:X) 2,∀ i j,coefficientValue 2 (Fp i j) =ᶠ[𝓝 x]
          (fun z => principalCoefficient (framedNormalMetric d.g₁ d.frame d.expMap y (d.radius y)) z i j)) ∧
        (strongDirichletOperator fixedSobolevCalculus 0 Fp).IsInvertible ∧
        ‖Da‖ ≤ CD ∧ ‖B‖ ≤ CB ∧
        ‖Da-sphereSobolevDegreeL-d.radius y • B.adjoint.comp (sphereSobolevInclusionL 1 0 (by norm_num))‖ ≤ CJ*(d.radius y)^2 ∧
        (∀ u v,⟪D u,sphereSobolevInclusionL 1 0 (by norm_num) v⟫_ℝ =
          ⟪sphereSobolevInclusionL 1 0 (by norm_num) u,Da v⟫_ℝ) ∧
        (∀ f : SphereSobolev (3/2:ℝ),D (sphereSobolevInclusionL (3/2:ℝ) 1 (by norm_num) f) =
          sphereSobolevZeroEquiv orthogonalSphereHarmonics denseSphereHarmonics
            (outwardRadialTraceL fixedSobolevCalculus fixedUnitBallValueTrace (strongPoissonL Fp f))) ∧
        ∀ a : X,∃ C : I → SmoothCoefficientJets 2,
          (∀ j,∀ z ∈ Metric.closedBall (0:X) 1,coefficientValue 2 (C j) =ᶠ[𝓝 z]
            (fun w => metricPair d.γ y
              ((normalizedParallelCenterJacobian d.γ d.expMap y
                (d.radius y • frameVector d.frame y w)-ContinuousLinearMap.id ℝ X) a) (d.frame y j))) ∧
          ‖(d.radius y)⁻¹ • boundaryGradientAdjointL C Da‖ ≤ CE*‖a‖*d.radius y ∧
          ∀ u : X → ℝ,HarmonicOnBall d.g₁ (closedBallImage d.γ d.expMap d.radius y) u →
          ∀ f : SphereSobolev (3/2:ℝ),
          (fixedBoundaryValueL f =ᵐ[sphereProbability] fun w : UnitSphere =>
            u (normalChart d.expMap d.frame y (d.radius y) w.val)) →
          (sphereSobolevZeroEquiv orthogonalSphereHarmonics denseSphereHarmonics).symm
            (boundaryGradientL C D (sphereSobolevInclusionL (3/2:ℝ) 1 (by norm_num) f))
              =ᵐ[sphereProbability] fun w : UnitSphere =>
                fderiv ℝ (ballPullback d.expMap d.radius y u) (frameVector d.frame y w.val)
                  ((normalizedParallelCenterJacobian d.γ d.expMap y
                    (d.radius y • frameVector d.frame y w.val)-ContinuousLinearMap.id ℝ X) a) := by
  have hTheorem := uniform_physical_center_error_gradient_adjoint_canonical hY hΩ hm K ρ c₀ M Cj hK hρ
  obtain ⟨η,CD,CB,CJ,CE,hη,hCD,hCB,hCJ,hCE,hProduce⟩ := hTheorem
  refine ⟨η,CD,CB,CJ,CE,hη,hCD,hCB,hCJ,hCE,?_⟩
  intro floor hf ε hε hSmall d hd y hy
  have hHere := hProduce floor hf ε hε hSmall d hd y hy
  obtain ⟨Fp,D,Da,B,hRep,hInv,hDa,hCanonical,hB,hTaylor,hPair,hD,hCenter⟩ := hHere
  exact ⟨Fp,D,Da,B,hRep,hInv,hDa,hB,hTaylor,hPair,hD,hCenter⟩

end ShrinkingSpheres
