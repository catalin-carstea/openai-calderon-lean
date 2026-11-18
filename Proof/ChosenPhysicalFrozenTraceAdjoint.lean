import Proof.ChosenPhysicalCenterErrorAdjoint
import Proof.PhysicalFixedCenterGradient
import Proof.FrozenTraceAdjointRealization

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3200000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter MeasureTheory
open scoped ContDiff Topology ENNReal InnerProductSpace
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.EnergyBridge OAI.AnisotropicCalderon.DirichletFamily
open OAI.AnisotropicCalderon.SphereHarmonic

/-- Frozen moving-trace adjunction retains an already chosen genuine radial
    response and its true adjoint. This is the physical identification needed
    by higher-jet packets, rather than an unrelated pointwise choice. -/
theorem uniform_frozen_trace_adjoint_of_chosen_radial {Y Ω : Set X} (hY : IsOpen Y) (hΩ : IsOpen Ω)
    {m : ℕ} (hm : 3 ≤ m) (K ρ c₀ : ℝ) (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ)
    (hK : 1 ≤ K) (hρ : 0 < ρ) :
    ∃ η CD CE : ℝ,∃ Q : SmoothCoefficientJets 2,
      0 < η ∧ 0 ≤ CD ∧ 0 ≤ CE ∧
      (∀ z ∈ Metric.closedBall (0:X) 1,coefficientValue 2 Q =ᶠ[𝓝 z] (fun _ => (1:ℝ))) ∧
      ∀ floor,1 ≤ floor → ∀ ε,0 ≤ ε → ε ≤ η → ∀ d,
      Admissible Y Ω K ρ c₀ M Cj floor ε d → ∀ y ∈ Y,
      ∀ R Da : SphereSobolev 1 →L[ℝ] SphereSobolev 0,
      RealizesActualMidpointRadialError d y R →
      (∀ u v,⟪(R+sphereSobolevDegreeL) u,sphereSobolevInclusionL 1 0 (by norm_num) v⟫_ℝ =
        ⟪sphereSobolevInclusionL 1 0 (by norm_num) u,Da v⟫_ℝ) →
      (∀ u : X → ℝ,HarmonicOnBall d.g₁ (closedBallImage d.γ d.expMap d.radius y) u →
        ∀ f : SphereSobolev (3/2:ℝ),
        (fixedBoundaryValueL f =ᵐ[sphereProbability] fun w : UnitSphere =>
          u (normalChart d.expMap d.frame y (d.radius y) w.val)) →
        (sphereSobolevZeroEquiv orthogonalSphereHarmonics denseSphereHarmonics).symm
          ((R+sphereSobolevDegreeL) (sphereSobolevInclusionL (3/2:ℝ) 1 (by norm_num) f)) =ᵐ[sphereProbability]
            fun w : UnitSphere => radialTrace d.expMap d.radius y (frameVector d.frame y w.val) u) →
      ‖Da‖ ≤ CD ∧ ∀ i : I,∃ C : I → SmoothCoefficientJets 2,
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
  obtain ⟨ηC,CD,CE,hηC,hCD,hCE,hCenter⟩ :=
    uniform_physical_center_error_of_chosen_radial hY hΩ hm K ρ c₀ M Cj hK hρ
  obtain ⟨ηF,Q,hηF,hQ,hFixed⟩ := uniform_physical_fixed_center_gradient hY hΩ hm K ρ c₀ M Cj hK hρ
  refine ⟨min ηC ηF,CD,CE,Q,lt_min hηC hηF,hCD,hCE,hQ,?_⟩
  intro floor hf ε hε hSmall d hd y hy R Da hReal hPair hRadial
  obtain ⟨Fp,hRep,hInv,hDa,hHigh,hCenterPoint⟩ :=
    hCenter floor hf ε hε (hSmall.trans (min_le_left _ _)) d hd y hy R Da hReal hPair
  refine ⟨hDa,?_⟩
  intro i
  obtain ⟨C,hCRep,hCBound,hCPhysical⟩ := hCenterPoint (axis i)
  refine ⟨C,hCRep,by simpa only [norm_axis,mul_one] using hCBound,?_⟩
  let P := fixedCenterCoefficient Q d.γ d.frame y (axis i)
  let D := R+sphereSobolevDegreeL
  let f := fderiv ℝ (fun x => Real.log (d.radius x)) y (axis i)
  have hAdjunction := movingBoundaryHorizontalL_adjoint P C D Da (d.radius y) f hPair
  have hForward : ∀ u : X → ℝ,HarmonicOnBall d.g₁ (closedBallImage d.γ d.expMap d.radius y) u →
      ∀ v : SphereSobolev (3/2:ℝ),
      (fixedBoundaryValueL v =ᵐ[sphereProbability] fun w : UnitSphere =>
        u (normalChart d.expMap d.frame y (d.radius y) w.val)) →
      (sphereSobolevZeroEquiv orthogonalSphereHarmonics denseSphereHarmonics).symm
        (movingBoundaryHorizontalL P C D (d.radius y) f (sphereSobolevInclusionL (3/2:ℝ) 1 (by norm_num) v)) =ᵐ[sphereProbability]
          fun w : UnitSphere => horizontal d.γ (fun p => u (endpoint d.expMap d.radius p))
            y (frameVector d.frame y w.val) (axis i) := by
    intro u hu v hBoundary
    have hPValue := hFixed floor hf ε hε (hSmall.trans (min_le_right _ _)) d hd y hy (axis i) Fp hRep hInv D hHigh u hu v hBoundary
    exact hd.movingBoundaryHorizontalL_value_ae hY hy (axis i) P C D _ u hu hPValue
      (hRadial u hu v hBoundary) (hCPhysical u hu v hBoundary)
  intro φ hφ L v hInput
  exact hd.frozen_adjoint_component_realization hy i (movingBoundaryHorizontalL P C D (d.radius y) f)
    (movingBoundaryHorizontalAdjointL P C Da (d.radius y) f) hAdjunction hForward φ hφ L v hInput

end ShrinkingSpheres
