import Proof.FrozenTraceAdjointRealization

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2600000
set_option maxSynthPendingDepth 15
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter MeasureTheory
open scoped ContDiff Topology ENNReal InnerProductSpace
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.EnergyBridge OAI.AnisotropicCalderon.DirichletFamily
open OAI.AnisotropicCalderon.SphereHarmonic

/-- The actual frozen moving-trace adjoint is the constructed physical L2
    adjoint on every smooth field component, uniformly for every admitted radius.
    The radial Taylor and center error witnesses are shared with that identity. -/
theorem uniform_frozen_trace_adjoint_realization_canonical {Y Ω : Set X} (hY : IsOpen Y) (hΩ : IsOpen Ω)
    {m : ℕ} (hm : 3 ≤ m) (K ρ c₀ : ℝ) (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ)
    (hK : 1 ≤ K) (hρ : 0 < ρ) :
    ∃ η CD CB CJ CE : ℝ,∃ Q : SmoothCoefficientJets 2,
      0 < η ∧ 0 ≤ CD ∧ 0 ≤ CB ∧ 0 ≤ CJ ∧ 0 ≤ CE ∧
      (∀ z ∈ Metric.closedBall (0:X) 1,coefficientValue 2 Q =ᶠ[𝓝 z] (fun _ => (1:ℝ))) ∧
      ∀ floor,1 ≤ floor → ∀ ε,0 ≤ ε → ε ≤ η → ∀ d,
      Admissible Y Ω K ρ c₀ M Cj floor ε d → ∀ y ∈ Y,
      ∃ Da : SphereSobolev 1 →L[ℝ] SphereSobolev 0,∃ B : SphereSobolev 0 →L[ℝ] SphereSobolev 0,
        ‖Da‖ ≤ CD ∧ B = firstRadialCorrectionL d y ∧ ‖B‖ ≤ CB ∧
        ‖Da-sphereSobolevDegreeL-d.radius y • B.adjoint.comp (sphereSobolevInclusionL 1 0 (by norm_num))‖ ≤ CJ*(d.radius y)^2 ∧
        ∀ i : I,∃ C : I → SmoothCoefficientJets 2,
          (∀ j,∀ z ∈ Metric.closedBall (0:X) 1,coefficientValue 2 (C j) =ᶠ[𝓝 z]
            (fun w => metricPair d.γ y
              ((normalizedParallelCenterJacobian d.γ d.expMap y
                (d.radius y • frameVector d.frame y w)-ContinuousLinearMap.id ℝ X) (axis i)) (d.frame y j))) ∧
          ‖(d.radius y)⁻¹ • boundaryGradientAdjointL C Da‖ ≤ CE*d.radius y ∧
          ∀ φ : Field,smoothNear φ (bundle Y d.γ) → ∀ L : ℂ →L[ℝ] ℝ,∀ v : SphereSobolev 1,
          ((sphereSobolevZeroEquiv orthogonalSphereHarmonics denseSphereHarmonics).symm
            (sphereSobolevInclusionL 1 0 (by norm_num) v) =ᵐ[sphereProbability]
              fun w : UnitSphere => L (φ (y,frameVector d.frame y w.val))) →
          (sphereSobolevZeroEquiv orthogonalSphereHarmonics denseSphereHarmonics).symm
            (movingBoundaryHorizontalAdjointL (fixedCenterCoefficient Q d.γ d.frame y (axis i)) C Da
              (d.radius y) (fderiv ℝ (fun x => Real.log (d.radius x)) y (axis i)) v) =ᵐ[sphereProbability]
                fun w : UnitSphere => L (adjointField d.adjoint i φ (y,frameVector d.frame y w.val)) := by
  have hTheorem := uniform_physical_moving_boundary_adjoint_canonical hY hΩ hm K ρ c₀ M Cj hK hρ
  obtain ⟨η,CD,CB,CJ,CE,Q,hη,hCD,hCB,hCJ,hCE,hQ,hPhysical⟩ := hTheorem
  refine ⟨η,CD,CB,CJ,CE,Q,hη,hCD,hCB,hCJ,hCE,hQ,?_⟩
  intro floor hf ε hε hSmall d hd y hy
  have hHere := hPhysical floor hf ε hε hSmall d hd y hy
  obtain ⟨Fp,D,Da,B,hRep,hInv,hDa,hCanonical,hB,hTaylor,hPair,hDirection⟩ := hHere
  refine ⟨Da,B,hDa,hCanonical,hB,hTaylor,?_⟩
  intro i
  have hIHere := hDirection (axis i)
  obtain ⟨C,hCRep,hCenter,hAdjunction,hForward⟩ := hIHere
  refine ⟨C,hCRep,?_,?_⟩
  · simpa only [norm_axis,mul_one] using hCenter
  · intro φ hφ L v hInput
    exact hd.frozen_adjoint_component_realization hy i
      (movingBoundaryHorizontalL (fixedCenterCoefficient Q d.γ d.frame y (axis i)) C D (d.radius y)
        (fderiv ℝ (fun x => Real.log (d.radius x)) y (axis i)))
      (movingBoundaryHorizontalAdjointL (fixedCenterCoefficient Q d.γ d.frame y (axis i)) C Da (d.radius y)
        (fderiv ℝ (fun x => Real.log (d.radius x)) y (axis i)))
      hAdjunction hForward φ hφ L v hInput


/-- The original existential interface, retained for existing callers. -/
theorem uniform_frozen_trace_adjoint_realization {Y Ω : Set X} (hY : IsOpen Y) (hΩ : IsOpen Ω)
    {m : ℕ} (hm : 3 ≤ m) (K ρ c₀ : ℝ) (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ)
    (hK : 1 ≤ K) (hρ : 0 < ρ) :
    ∃ η CD CB CJ CE : ℝ,∃ Q : SmoothCoefficientJets 2,
      0 < η ∧ 0 ≤ CD ∧ 0 ≤ CB ∧ 0 ≤ CJ ∧ 0 ≤ CE ∧
      (∀ z ∈ Metric.closedBall (0:X) 1,coefficientValue 2 Q =ᶠ[𝓝 z] (fun _ => (1:ℝ))) ∧
      ∀ floor,1 ≤ floor → ∀ ε,0 ≤ ε → ε ≤ η → ∀ d,
      Admissible Y Ω K ρ c₀ M Cj floor ε d → ∀ y ∈ Y,
      ∃ Da : SphereSobolev 1 →L[ℝ] SphereSobolev 0,∃ B : SphereSobolev 0 →L[ℝ] SphereSobolev 0,
        ‖Da‖ ≤ CD ∧ ‖B‖ ≤ CB ∧
        ‖Da-sphereSobolevDegreeL-d.radius y • B.adjoint.comp (sphereSobolevInclusionL 1 0 (by norm_num))‖ ≤ CJ*(d.radius y)^2 ∧
        ∀ i : I,∃ C : I → SmoothCoefficientJets 2,
          (∀ j,∀ z ∈ Metric.closedBall (0:X) 1,coefficientValue 2 (C j) =ᶠ[𝓝 z]
            (fun w => metricPair d.γ y
              ((normalizedParallelCenterJacobian d.γ d.expMap y
                (d.radius y • frameVector d.frame y w)-ContinuousLinearMap.id ℝ X) (axis i)) (d.frame y j))) ∧
          ‖(d.radius y)⁻¹ • boundaryGradientAdjointL C Da‖ ≤ CE*d.radius y ∧
          ∀ φ : Field,smoothNear φ (bundle Y d.γ) → ∀ L : ℂ →L[ℝ] ℝ,∀ v : SphereSobolev 1,
          ((sphereSobolevZeroEquiv orthogonalSphereHarmonics denseSphereHarmonics).symm
            (sphereSobolevInclusionL 1 0 (by norm_num) v) =ᵐ[sphereProbability]
              fun w : UnitSphere => L (φ (y,frameVector d.frame y w.val))) →
          (sphereSobolevZeroEquiv orthogonalSphereHarmonics denseSphereHarmonics).symm
            (movingBoundaryHorizontalAdjointL (fixedCenterCoefficient Q d.γ d.frame y (axis i)) C Da
              (d.radius y) (fderiv ℝ (fun x => Real.log (d.radius x)) y (axis i)) v) =ᵐ[sphereProbability]
                fun w : UnitSphere => L (adjointField d.adjoint i φ (y,frameVector d.frame y w.val)) := by
  have hTheorem := uniform_frozen_trace_adjoint_realization_canonical hY hΩ hm K ρ c₀ M Cj hK hρ
  obtain ⟨η,CD,CB,CJ,CE,Q,hη,hCD,hCB,hCJ,hCE,hQ,hProduce⟩ := hTheorem
  refine ⟨η,CD,CB,CJ,CE,Q,hη,hCD,hCB,hCJ,hCE,hQ,?_⟩
  intro floor hf ε hε hSmall d hd y hy
  have hHere := hProduce floor hf ε hε hSmall d hd y hy
  obtain ⟨Da,B,hDa,hCanonical,hB,hTaylor,hDirection⟩ := hHere
  exact ⟨Da,B,hDa,hB,hTaylor,hDirection⟩

end ShrinkingSpheres
