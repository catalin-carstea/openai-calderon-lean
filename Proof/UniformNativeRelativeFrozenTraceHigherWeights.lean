import Proof.NativeRelativePhysicalRadialIdentification
import Proof.UniformNativeRelativeFrozenTraceData
import Proof.RelativeCenterErrorCoefficientFamily
import Proof.BoundaryGradientCoefficientLocality

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
    Its actual center-error coefficients are the SAME gained joint/horizontal families. -/
theorem uniform_native_relative_frozen_trace_higher_weights {Y Ω : Set X}
    (hY : IsOpen Y) (hΩ : IsOpen Ω) (hSub : Y ⊆ Ω) {m : ℕ} (hm : 10 ≤ m)
    (K ρ c₀ : ℝ) (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ) (hK : 1 ≤ K) (hρ : 0 < ρ) :
    ∃ η CF CA CM CQ CI CW CD CE CC CH : ℝ,∃ F0 : SmoothCoefficientMatrix 2,∃ Q : SmoothCoefficientJets 2,
      0 < η ∧ η ≤ 1 ∧ 1 ≤ CF ∧ 1 ≤ CA ∧ 1 ≤ CM ∧ 1 ≤ CQ ∧ 0 ≤ CI ∧ 0 ≤ CW ∧ 0 ≤ CD ∧ 0 ≤ CE ∧ 1 ≤ CC ∧ 1 ≤ CH ∧
      (∀ z ∈ Metric.closedBall (0:X) 2,coefficientMatrixField 2 F0 z = 1) ∧
      (∀ z ∈ Metric.closedBall (0:X) 1,coefficientValue 2 Q =ᶠ[𝓝 z] (fun _ => (1:ℝ))) ∧
      ∀ floor,1 ≤ floor → ∀ ε,0 ≤ ε → ε ≤ η → ∀ d,
      Admissible Y Ω K ρ c₀ M Cj floor ε d → ∀ y ∈ Y,
      ∃ s : NativeRelativeHorizontalTaylorData Y Ω d y F0 CQ CI CW CF CA CM,
        RealizesActualMidpointRadialError d y (s.response.response ((y,frameVectorLinear d.frame y),0)) ∧
        (∀ u v,⟪s.radialL u,sphereSobolevInclusionL 1 0 (by norm_num) v⟫_ℝ =
          ⟪sphereSobolevInclusionL 1 0 (by norm_num) u,s.radialAdjointL v⟫_ℝ) ∧
        ‖s.radialAdjointL‖ ≤ CD ∧
        ∀ i : I,∃ C : (j : I) → RelativeCenterErrorCoefficientFamily d y (axis i) j CC CH,
          ‖(d.radius y)⁻¹ • boundaryGradientAdjointL (fun j => (C j).pointCoefficient) s.radialAdjointL‖ ≤ CE*d.radius y ∧
          ∀ φ : Field,smoothNear φ (bundle Y d.γ) → ∀ L : ℂ →L[ℝ] ℝ,∀ v : SphereSobolev 1,
          ((sphereSobolevZeroEquiv orthogonalSphereHarmonics denseSphereHarmonics).symm
            (sphereSobolevInclusionL 1 0 (by norm_num) v) =ᵐ[sphereProbability]
              fun w : UnitSphere => L (φ (y,frameVector d.frame y w.val))) →
          (sphereSobolevZeroEquiv orthogonalSphereHarmonics denseSphereHarmonics).symm
            (movingBoundaryHorizontalAdjointL (fixedCenterCoefficient Q d.γ d.frame y (axis i)) (fun j => (C j).pointCoefficient) s.radialAdjointL
              (d.radius y) (fderiv ℝ (fun x => Real.log (d.radius x)) y (axis i)) v) =ᵐ[sphereProbability]
                fun w : UnitSphere => L (adjointField d.adjoint i φ (y,frameVector d.frame y w.val)) := by
  obtain ⟨ηF,CF,CA,CM,CQ,CI,CW,CD,CE,F0,Q,hηF,hηF1,hCF,hCA,hCM,hCQ,hCI,hCW,hCD,hCE,hF0,hQ,hFrozen⟩ :=
    uniform_native_relative_frozen_trace_data hY hΩ hSub (by omega) K ρ c₀ M Cj hK hρ
  obtain ⟨ηC,CC,CH,hηC,hηC1,hCC,hCH,hCoefficients⟩ :=
    uniform_relative_center_error_coefficient_families hY hΩ hSub hm K ρ c₀ M Cj hK hρ
  refine ⟨min ηF ηC,CF,CA,CM,CQ,CI,CW,CD,CE,CC,CH,F0,Q,lt_min hηF hηC,
    (min_le_left _ _).trans hηF1,hCF,hCA,hCM,hCQ,hCI,hCW,hCD,hCE,hCC,hCH,hF0,hQ,?_⟩
  intro floor hf ε hε hSmall d hd y hy
  obtain ⟨s,hReal,hPair,hDa,hCenter⟩ := hFrozen floor hf ε hε (hSmall.trans (min_le_left _ _)) d hd y hy
  refine ⟨s,hReal,hPair,hDa,?_⟩
  intro i
  obtain ⟨Cold,hColdRep,hColdBound,hColdPhysical⟩ := hCenter i
  let C : (j : I) → RelativeCenterErrorCoefficientFamily d y (axis i) j CC CH := fun j =>
    Classical.choice (hCoefficients floor hf ε hε (hSmall.trans (min_le_right _ _)) d hd y hy (axis i) j)
  have hValues (j : I) (w : UnitSphere) : coefficientValue 2 (C j).pointCoefficient w.val =
      coefficientValue 2 (Cold j) w.val := by
    have hw1 : w.val ∈ Metric.closedBall (0:X) 1 := by
      have hn : ‖w.val‖=1 := by simp [UnitSphere,Metric.sphere,dist_eq_norm]
      simp [Metric.mem_closedBall,dist_zero_right,hn]
    exact ((C j).point_coefficient_actual w.val
      (Metric.closedBall_subset_closedBall (by norm_num) hw1)).eq_of_nhds.trans
        (hColdRep j w.val hw1).eq_of_nhds.symm
  have hAdj := (boundaryGradientL_and_adjoint_congr_sphere (fun j => (C j).pointCoefficient)
    Cold hValues s.radialL s.radialAdjointL).2
  refine ⟨C,?_,?_⟩
  · rw [hAdj]
    exact hColdBound
  · intro φ hφ L v hInput
    have hMove : movingBoundaryHorizontalAdjointL (fixedCenterCoefficient Q d.γ d.frame y (axis i))
        (fun j => (C j).pointCoefficient) s.radialAdjointL (d.radius y)
        (fderiv ℝ (fun x => Real.log (d.radius x)) y (axis i)) =
      movingBoundaryHorizontalAdjointL (fixedCenterCoefficient Q d.γ d.frame y (axis i)) Cold
        s.radialAdjointL (d.radius y) (fderiv ℝ (fun x => Real.log (d.radius x)) y (axis i)) := by
      simp only [movingBoundaryHorizontalAdjointL,hAdj]
    rw [hMove]
    exact hColdPhysical φ hφ L v hInput

end ShrinkingSpheres
