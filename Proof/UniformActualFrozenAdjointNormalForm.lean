import Proof.NativeActualRadialPointIdentity
import Proof.ActualFirstAdjointErrorFamily
import Proof.UniformNativeRelativeFrozenTraceHigherWeights
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3200000
set_option maxSynthPendingDepth 30
set_option maxRecDepth 2200
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
open Set Filter MeasureTheory
open scoped ContDiff Topology InnerProductSpace
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.DirichletFamily
open OAI.AnisotropicCalderon.SphereHarmonic

/-- Exact physical trace-adjoint normal form using the SAME globally chosen
    radial pair and complete error family, for every admitted profile and frame. -/
theorem uniform_actual_frozen_adjoint_normal_form {Y Ω : Set X}
    (hY : IsOpen Y) (hΩ : IsOpen Ω) (hSub : Y ⊆ Ω) {m : ℕ} (hm : 10 ≤ m)
    (K ρ c₀ : ℝ) (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ) (hK : 1 ≤ K) (hρ : 0 < ρ) :
    ∃ η : ℝ,∃ Q : SmoothCoefficientJets 2,0 < η ∧
      (∀ z ∈ Metric.closedBall (0:X) 1,coefficientValue 2 Q =ᶠ[𝓝 z] (fun _ => (1:ℝ))) ∧
      ∀ floor,1 ≤ floor → ∀ ε,0 ≤ ε → ε ≤ η → ∀ d,
      Admissible Y Ω K ρ c₀ M Cj floor ε d →
      ∀ R A : X → SphereSobolev 1 →L[ℝ] SphereSobolev 0,
      (∀ x ∈ Y,RealizesActualMidpointRadialError d x (R x)) →
      (∀ x ∈ Y,∀ u v,⟪(R x+sphereSobolevDegreeL) u,sphereSobolevInclusionL 1 0 (by norm_num) v⟫_ℝ =
        ⟪sphereSobolevInclusionL 1 0 (by norm_num) u,A x v⟫_ℝ) →
      ∀ i : I,∀ G : X → SphereSobolev 1 →L[ℝ] SphereSobolev 0,
      (∀ x ∈ Y,RealizesActualCenterGradientAdjoint d x (axis i) (A x) (G x)) →
      ∀ y ∈ Y,∀ φ : Field,smoothNear φ (bundle Y d.γ) → ∀ L : ℂ →L[ℝ] ℝ,∀ v : SphereSobolev 1,
      ((sphereSobolevZeroEquiv orthogonalSphereHarmonics denseSphereHarmonics).symm
        (sphereSobolevInclusionL 1 0 (by norm_num) v) =ᵐ[sphereProbability]
          fun w : UnitSphere => L (φ (y,frameVector d.frame y w.val))) →
      (sphereSobolevZeroEquiv orthogonalSphereHarmonics denseSphereHarmonics).symm
        (modelBoundaryAdjointL (fixedCenterCoefficient Q d.γ d.frame y (axis i)) (d.radius y)
            (fderiv ℝ (fun x => Real.log (d.radius x)) y (axis i)) v+
          firstBoundaryAdjointCorrectionL (fixedCenterCoefficient Q d.γ d.frame y (axis i))
            (firstRadialCorrectionL d y) (d.radius y) (fderiv ℝ (fun x => Real.log (d.radius x)) y (axis i))
            (sphereSobolevInclusionL 1 0 (by norm_num) v)+actualFirstAdjointErrorFamily d (axis i) A G y v) =ᵐ[sphereProbability]
        fun w : UnitSphere => L (adjointField d.adjoint i φ (y,frameVector d.frame y w.val)) := by
  obtain ⟨η,CF,CA,CM,CQ,CI,CW,CD,CE,CC,CH,F0,Q,hη,hη1,hCF,hCA,hCM,hCQ,hCI,hCW,hCD,hCE,hCC,hCH,
    hF0,hQ,hFrozen⟩ := uniform_native_relative_frozen_trace_higher_weights hY hΩ hSub hm K ρ c₀ M Cj hK hρ
  refine ⟨η,Q,hη,hQ,?_⟩
  intro floor hf ε hε hSmall d hd R A hR hA i G hG y hy φ hφ L v hInput
  obtain ⟨s,hReal,hPair,hDa,hCenter⟩ := hFrozen floor hf ε hε hSmall d hd y hy
  have hAeq := s.actual_adjoint_point hΩ hd.1 (zero_lt_one.trans_le hK) (hSub hy)
    (R y) (A y) (hR y hy) (hA y hy) hPair
  obtain ⟨C,hCenterBound,hPhysical⟩ := hCenter i
  let W : I → SmoothCoefficientJets 2 := fun j => (C j).pointCoefficient
  have hW (j : I) (w : UnitSphere) : coefficientValue 2 (W j) w.val = actualCenterErrorWeight d y (axis i) j w.val := by
    exact ((C j).point_coefficient_actual w.val
      (Metric.closedBall_subset_closedBall (by norm_num) (Metric.sphere_subset_closedBall w.property))).eq_of_nhds
  have hE := actualFirstAdjointErrorFamily_physical hd.1 (hSub hy) (axis i) A G (hG y hy) Q hQ W hW
  have hOp := movingBoundaryHorizontalAdjointL_normal_form (fixedCenterCoefficient Q d.γ d.frame y (axis i))
    W (A y) (firstRadialCorrectionL d y) (d.radius y) (fderiv ℝ (fun x => Real.log (d.radius x)) y (axis i))
    (hd.2.2.2.2.1.2 y hy).1.ne'
  rw [← hE] at hOp
  have hOut := hPhysical φ hφ L v hInput
  rw [← hAeq,hOp] at hOut
  simpa only [_root_.add_apply,ContinuousLinearMap.comp_apply] using hOut
end ShrinkingSpheres
