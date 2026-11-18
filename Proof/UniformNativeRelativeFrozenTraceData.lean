import Proof.NativeRelativePhysicalRadialIdentification
import Proof.ChosenPhysicalFrozenTraceAdjoint

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4200000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter MeasureTheory
open scoped ContDiff Topology ENNReal InnerProductSpace Matrix.Norms.Elementwise
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.EnergyBridge OAI.AnisotropicCalderon.DirichletFamily
open OAI.AnisotropicCalderon.SphereHarmonic

/-- The chosen joint/horizontal Taylor packet is identified with the actual
    frozen moving-trace adjoint, with its SAME radial response and adjoint.
    The only remaining geometric weight choice is displayed explicitly. -/
theorem uniform_native_relative_frozen_trace_data {Y Ω : Set X}
    (hY : IsOpen Y) (hΩ : IsOpen Ω) (hSub : Y ⊆ Ω) {m : ℕ} (hm : 8 ≤ m)
    (K ρ c₀ : ℝ) (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ) (hK : 1 ≤ K) (hρ : 0 < ρ) :
    ∃ η CF CA CM CQ CI CW CD CE : ℝ,∃ F0 : SmoothCoefficientMatrix 2,∃ Q : SmoothCoefficientJets 2,
      0 < η ∧ η ≤ 1 ∧ 1 ≤ CF ∧ 1 ≤ CA ∧ 1 ≤ CM ∧ 1 ≤ CQ ∧ 0 ≤ CI ∧ 0 ≤ CW ∧ 0 ≤ CD ∧ 0 ≤ CE ∧
      (∀ z ∈ Metric.closedBall (0:X) 2,coefficientMatrixField 2 F0 z = 1) ∧
      (∀ z ∈ Metric.closedBall (0:X) 1,coefficientValue 2 Q =ᶠ[𝓝 z] (fun _ => (1:ℝ))) ∧
      ∀ floor,1 ≤ floor → ∀ ε,0 ≤ ε → ε ≤ η → ∀ d,
      Admissible Y Ω K ρ c₀ M Cj floor ε d → ∀ y ∈ Y,
      ∃ s : NativeRelativeHorizontalTaylorData Y Ω d y F0 CQ CI CW CF CA CM,
        RealizesActualMidpointRadialError d y (s.response.response ((y,frameVectorLinear d.frame y),0)) ∧
        (∀ u v,⟪s.radialL u,sphereSobolevInclusionL 1 0 (by norm_num) v⟫_ℝ =
          ⟪sphereSobolevInclusionL 1 0 (by norm_num) u,s.radialAdjointL v⟫_ℝ) ∧
        ‖s.radialAdjointL‖ ≤ CD ∧
        ∀ i : I,∃ C : I → SmoothCoefficientJets 2,
          (∀ j,∀ z ∈ Metric.closedBall (0:X) 1,coefficientValue 2 (C j) =ᶠ[𝓝 z]
            (fun w => metricPair d.γ y
              ((normalizedParallelCenterJacobian d.γ d.expMap y
                (d.radius y • frameVector d.frame y w)-ContinuousLinearMap.id ℝ X) (axis i)) (d.frame y j))) ∧
          ‖(d.radius y)⁻¹ • boundaryGradientAdjointL C s.radialAdjointL‖ ≤ CE*d.radius y ∧
          ∀ φ : Field,smoothNear φ (bundle Y d.γ) → ∀ L : ℂ →L[ℝ] ℝ,∀ v : SphereSobolev 1,
          ((sphereSobolevZeroEquiv orthogonalSphereHarmonics denseSphereHarmonics).symm
            (sphereSobolevInclusionL 1 0 (by norm_num) v) =ᵐ[sphereProbability]
              fun w : UnitSphere => L (φ (y,frameVector d.frame y w.val))) →
          (sphereSobolevZeroEquiv orthogonalSphereHarmonics denseSphereHarmonics).symm
            (movingBoundaryHorizontalAdjointL (fixedCenterCoefficient Q d.γ d.frame y (axis i)) C s.radialAdjointL
              (d.radius y) (fderiv ℝ (fun x => Real.log (d.radius x)) y (axis i)) v) =ᵐ[sphereProbability]
                fun w : UnitSphere => L (adjointField d.adjoint i φ (y,frameVector d.frame y w.val)) := by
  obtain ⟨ηN,CF,CA,CM,CQ,CI,CW,F0,hηN,hηN1,hCF,hCA,hCM,hCQ,hCI,hCW,hF0,hNative⟩ :=
    uniform_native_relative_physical_radial_data hY hΩ hSub hm K ρ c₀ M Cj hK hρ
  obtain ⟨ηF,CD,CE,Q,hηF,hCD,hCE,hQ,hFrozen⟩ :=
    uniform_frozen_trace_adjoint_of_chosen_radial (Y:=Y) hY hΩ (by omega) K ρ c₀ M Cj hK hρ
  refine ⟨min ηN ηF,CF,CA,CM,CQ,CI,CW,CD,CE,F0,Q,lt_min hηN hηF,(min_le_left _ _).trans hηN1,
    hCF,hCA,hCM,hCQ,hCI,hCW,hCD,hCE,hF0,hQ,?_⟩
  intro floor hf ε hε hSmall d hd y hy
  obtain ⟨s,hPair,hPhysical⟩ := hNative floor hf ε hε (hSmall.trans (min_le_left _ _)) d hd y hy
  have hReal := s.realizesActualMidpointRadialError hΩ hd (zero_lt_one.trans_le hK) hy
  have hHere := hFrozen floor hf ε hε (hSmall.trans (min_le_right _ _)) d hd y hy
    (s.response.response ((y,frameVectorLinear d.frame y),0)) s.radialAdjointL hReal hPair hPhysical
  exact ⟨s,hReal,hPair,hHere⟩

end ShrinkingSpheres
