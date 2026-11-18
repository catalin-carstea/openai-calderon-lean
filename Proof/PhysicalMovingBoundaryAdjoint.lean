import Proof.PhysicalFixedCenterGradient

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

/-- A genuine moving-boundary action and its exact physical L2 adjoint for
    every admitted radius, with shared actual Dirichlet witnesses. The center
    error adjoint has a common radius-linear bound. -/
theorem uniform_physical_moving_boundary_adjoint_canonical {Y Ω : Set X} (hY : IsOpen Y) (hΩ : IsOpen Ω)
    {m : ℕ} (hm : 3 ≤ m) (K ρ c₀ : ℝ) (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ)
    (hK : 1 ≤ K) (hρ : 0 < ρ) :
    ∃ η CD CB CJ CE : ℝ,∃ Q : SmoothCoefficientJets 2,
      0 < η ∧ 0 ≤ CD ∧ 0 ≤ CB ∧ 0 ≤ CJ ∧ 0 ≤ CE ∧
      (∀ z ∈ Metric.closedBall (0:X) 1,coefficientValue 2 Q =ᶠ[𝓝 z] (fun _ => (1:ℝ))) ∧
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
        ∀ a : X,∃ C : I → SmoothCoefficientJets 2,
          (∀ j,∀ z ∈ Metric.closedBall (0:X) 1,coefficientValue 2 (C j) =ᶠ[𝓝 z]
            (fun w => metricPair d.γ y
              ((normalizedParallelCenterJacobian d.γ d.expMap y
                (d.radius y • frameVector d.frame y w)-ContinuousLinearMap.id ℝ X) a) (d.frame y j))) ∧
          ‖(d.radius y)⁻¹ • boundaryGradientAdjointL C Da‖ ≤ CE*‖a‖*d.radius y ∧
          (∀ u v,⟪movingBoundaryHorizontalL (fixedCenterCoefficient Q d.γ d.frame y a) C D
              (d.radius y) (fderiv ℝ (fun x => Real.log (d.radius x)) y a) u,
              sphereSobolevInclusionL 1 0 (by norm_num) v⟫_ℝ =
            ⟪sphereSobolevInclusionL 1 0 (by norm_num) u,
              movingBoundaryHorizontalAdjointL (fixedCenterCoefficient Q d.γ d.frame y a) C Da
                (d.radius y) (fderiv ℝ (fun x => Real.log (d.radius x)) y a) v⟫_ℝ) ∧
          ∀ u : X → ℝ,HarmonicOnBall d.g₁ (closedBallImage d.γ d.expMap d.radius y) u →
          ∀ f : SphereSobolev (3/2:ℝ),
          (fixedBoundaryValueL f =ᵐ[sphereProbability] fun w : UnitSphere =>
            u (normalChart d.expMap d.frame y (d.radius y) w.val)) →
          (sphereSobolevZeroEquiv orthogonalSphereHarmonics denseSphereHarmonics).symm
            (movingBoundaryHorizontalL (fixedCenterCoefficient Q d.γ d.frame y a) C D (d.radius y)
              (fderiv ℝ (fun x => Real.log (d.radius x)) y a)
                (sphereSobolevInclusionL (3/2:ℝ) 1 (by norm_num) f)) =ᵐ[sphereProbability]
                  fun w : UnitSphere => horizontal d.γ (fun p => u (endpoint d.expMap d.radius p))
                    y (frameVector d.frame y w.val) a := by
  have hErrorTheorem := uniform_physical_center_error_gradient_adjoint_canonical hY hΩ hm K ρ c₀ M Cj hK hρ
  obtain ⟨ηE,CD,CB,CJ,CE,hηE,hCD,hCB,hCJ,hCE,hError⟩ := hErrorTheorem
  have hFixedTheorem := uniform_physical_fixed_center_gradient hY hΩ hm K ρ c₀ M Cj hK hρ
  obtain ⟨ηF,Q,hηF,hQ,hFixed⟩ := hFixedTheorem
  have hPhysicalTheorem := uniform_physical_strong_poisson_realization (Y:=Y) hΩ hm K ρ c₀ M Cj hK hρ
  obtain ⟨ηP,hηP,hPhysical⟩ := hPhysicalTheorem
  refine ⟨min ηE (min ηF ηP),CD,CB,CJ,CE,Q,lt_min hηE (lt_min hηF hηP),hCD,hCB,hCJ,hCE,hQ,?_⟩
  intro floor hf ε hε hSmall d hd y hy
  have hEHere := hError floor hf ε hε (hSmall.trans (min_le_left _ _)) d hd y hy
  obtain ⟨Fp,D,Da,B,hRep,hInv,hDa,hCanonical,hB,hTaylor,hPair,hD,hCenter⟩ := hEHere
  refine ⟨Fp,D,Da,B,hRep,hInv,hDa,hCanonical,hB,hTaylor,hPair,?_⟩
  intro a
  have hCHere := hCenter a
  obtain ⟨C,hCRep,hCBound,hCPhysical⟩ := hCHere
  refine ⟨C,hCRep,hCBound,?_,?_⟩
  · exact movingBoundaryHorizontalL_adjoint _ C D Da _ _ hPair
  · intro u hu f hBoundary
    have hPValues := hFixed floor hf ε hε
      (hSmall.trans ((min_le_right _ _).trans (min_le_left _ _))) d hd y hy a Fp hRep hInv D hD u hu f hBoundary
    have hCValues := hCPhysical u hu f hBoundary
    have hPHere := hPhysical floor hf ε hε
      (hSmall.trans ((min_le_right _ _).trans (min_le_right _ _))) d hd y hy Fp hRep hInv u hu f hBoundary
    obtain ⟨U,hCompact,hNear,hIdent⟩ := hPHere
    let Z := sphereSobolevZeroEquiv orthogonalSphereHarmonics denseSphereHarmonics
    have hDValue : Z.symm (D (sphereSobolevInclusionL (3/2:ℝ) 1 (by norm_num) f)) =
        outwardRadialTraceL fixedSobolevCalculus fixedUnitBallValueTrace (strongPoissonL Fp f) :=
      (congrArg Z.symm (hD f)).trans (Z.symm_apply_apply _)
    have hActual := hd.outwardRadialTrace_representative_ae hY hy u hu U hNear
    rw [hIdent] at hActual
    have hRadial := hDValue.symm ▸ hActual
    exact hd.movingBoundaryHorizontalL_value_ae hY hy a _ C D _ u hu hPValues hRadial hCValues


/-- The original existential interface, retained for existing callers. -/
theorem uniform_physical_moving_boundary_adjoint {Y Ω : Set X} (hY : IsOpen Y) (hΩ : IsOpen Ω)
    {m : ℕ} (hm : 3 ≤ m) (K ρ c₀ : ℝ) (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ)
    (hK : 1 ≤ K) (hρ : 0 < ρ) :
    ∃ η CD CB CJ CE : ℝ,∃ Q : SmoothCoefficientJets 2,
      0 < η ∧ 0 ≤ CD ∧ 0 ≤ CB ∧ 0 ≤ CJ ∧ 0 ≤ CE ∧
      (∀ z ∈ Metric.closedBall (0:X) 1,coefficientValue 2 Q =ᶠ[𝓝 z] (fun _ => (1:ℝ))) ∧
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
        ∀ a : X,∃ C : I → SmoothCoefficientJets 2,
          (∀ j,∀ z ∈ Metric.closedBall (0:X) 1,coefficientValue 2 (C j) =ᶠ[𝓝 z]
            (fun w => metricPair d.γ y
              ((normalizedParallelCenterJacobian d.γ d.expMap y
                (d.radius y • frameVector d.frame y w)-ContinuousLinearMap.id ℝ X) a) (d.frame y j))) ∧
          ‖(d.radius y)⁻¹ • boundaryGradientAdjointL C Da‖ ≤ CE*‖a‖*d.radius y ∧
          (∀ u v,⟪movingBoundaryHorizontalL (fixedCenterCoefficient Q d.γ d.frame y a) C D
              (d.radius y) (fderiv ℝ (fun x => Real.log (d.radius x)) y a) u,
              sphereSobolevInclusionL 1 0 (by norm_num) v⟫_ℝ =
            ⟪sphereSobolevInclusionL 1 0 (by norm_num) u,
              movingBoundaryHorizontalAdjointL (fixedCenterCoefficient Q d.γ d.frame y a) C Da
                (d.radius y) (fderiv ℝ (fun x => Real.log (d.radius x)) y a) v⟫_ℝ) ∧
          ∀ u : X → ℝ,HarmonicOnBall d.g₁ (closedBallImage d.γ d.expMap d.radius y) u →
          ∀ f : SphereSobolev (3/2:ℝ),
          (fixedBoundaryValueL f =ᵐ[sphereProbability] fun w : UnitSphere =>
            u (normalChart d.expMap d.frame y (d.radius y) w.val)) →
          (sphereSobolevZeroEquiv orthogonalSphereHarmonics denseSphereHarmonics).symm
            (movingBoundaryHorizontalL (fixedCenterCoefficient Q d.γ d.frame y a) C D (d.radius y)
              (fderiv ℝ (fun x => Real.log (d.radius x)) y a)
                (sphereSobolevInclusionL (3/2:ℝ) 1 (by norm_num) f)) =ᵐ[sphereProbability]
                  fun w : UnitSphere => horizontal d.γ (fun p => u (endpoint d.expMap d.radius p))
                    y (frameVector d.frame y w.val) a := by
  have hTheorem := uniform_physical_moving_boundary_adjoint_canonical hY hΩ hm K ρ c₀ M Cj hK hρ
  obtain ⟨η,CD,CB,CJ,CE,Q,hη,hCD,hCB,hCJ,hCE,hQ,hProduce⟩ := hTheorem
  refine ⟨η,CD,CB,CJ,CE,Q,hη,hCD,hCB,hCJ,hCE,hQ,?_⟩
  intro floor hf ε hε hSmall d hd y hy
  have hHere := hProduce floor hf ε hε hSmall d hd y hy
  obtain ⟨Fp,D,Da,B,hRep,hInv,hDa,hCanonical,hB,hTaylor,hPair,hDirection⟩ := hHere
  exact ⟨Fp,D,Da,B,hRep,hInv,hDa,hB,hTaylor,hPair,hDirection⟩

end ShrinkingSpheres
