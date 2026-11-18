import Proof.StrongActualSecondTraceAssembly
import Proof.UniformFrameCovariantEndpoints
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3600000
set_option maxSynthPendingDepth 30
set_option maxRecDepth 2400
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
open Set Filter
open scoped ContDiff Topology InnerProductSpace
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.DirichletFamily OAI.AnisotropicCalderon.SphereHarmonic

/-- One shared physical second-trace witness retains its actual error graph,
    coarse norm and genuine balanced endpoint bounds before choosing a test. -/
theorem uniform_actual_second_trace_with_tensor_endpoints {Y Ω : Set X}
    (hY : IsOpen Y) (hΩ : IsOpen Ω) (hSub : Y ⊆ Ω) {m : ℕ} (hm : 10 ≤ m)
    (K ρ c₀ : ℝ) (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ) (hK : 1 ≤ K) (hρ : 0 < ρ)
    (C0 : ℝ) (hC0 : 0 ≤ C0) :
    ∃ η CE : ℝ,0 < η ∧ η ≤ 1 ∧ 0 ≤ CE ∧
      ∀ floor,1 ≤ floor → ∀ ε,0 ≤ ε → ε ≤ η → ∀ d,
      Admissible Y Ω K ρ c₀ M Cj floor ε d →
      ∀ R A : X → SphereSobolev 1 →L[ℝ] SphereSobolev 0,
      ContDiffOn ℝ ∞ A Y →
      (∀ x ∈ Y,RealizesActualMidpointRadialError d x (R x)) →
      (∀ x ∈ Y,∀ u v,⟪(R x+sphereSobolevDegreeL) u,sphereSobolevInclusionL 1 0 (by norm_num) v⟫_ℝ =
        ⟪sphereSobolevInclusionL 1 0 (by norm_num) u,A x v⟫_ℝ) →
      ∀ G : I → X → SphereSobolev 1 →L[ℝ] SphereSobolev 0,
      (∀ a,ContDiffOn ℝ ∞ (G a) Y) →
      (∀ a,∀ x ∈ Y,RealizesActualCenterGradientAdjoint d x (axis a) (A x) (G a x)) →
      (∀ a,∀ x ∈ Y,‖actualFirstAdjointErrorFamily d (axis a) A (G a) x‖ ≤ C0*d.radius x) →
      ∃ S : I → I → X → SphereSobolev 1 →L[ℝ] SphereSobolev 0,
        (∀ i j,ContDiffOn ℝ ∞ (S i j) Y) ∧
        (∀ y ∈ Y,∀ i j,CoarseCovariantRotationGraph d y (d.frame y i)
          (actualFrameFirstAdjointErrorFamily d A G j)
          ((∑ k : I,frameConnectionCoefficient d.γ d.frame y (d.frame y i) j k •
            actualFrameFirstAdjointErrorFamily d A G k y)+S i j y)) ∧
        (∀ y ∈ Y,∀ i j,‖S i j y‖ ≤ CE*d.radius y*beta d.γ d.radius y) ∧
        (∀ y ∈ Y,∀ i j,
          ∃ Lo : SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ)),
          ∃ Hi : SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ),
            (sphereSobolevInclusionL 0 (-(1/2:ℝ)) (by norm_num)).comp (S i j y)=
              Lo.comp (sphereSobolevInclusionL 1 (1/2:ℝ) (by norm_num)) ∧
            (sphereSobolevInclusionL (1/2:ℝ) 0 (by norm_num)).comp Hi=
              (S i j y).comp (sphereSobolevInclusionL (3/2:ℝ) 1 (by norm_num)) ∧
            ‖Lo‖ ≤ CE*d.radius y*beta d.γ d.radius y ∧
            ‖Hi‖ ≤ CE*d.radius y*beta d.γ d.radius y) ∧
        ∀ φ : Field,smoothNear φ (bundle Y d.γ) →
        (∃ T : Set X,IsCompact T ∧ T ⊆ Y ∧ ∀ x ∈ Y \ T,∀ w ∈ sphereAt d.γ x,φ (x,w)=0) →
        ∀ L : ℂ →L[ℝ] ℝ,∀ F : X × X → ℝ,∀ hF : ContDiff ℝ ∞ F,
        (∀ x ∈ Y,∀ w : UnitSphere,F (x,w.val)=L (φ (x,frameVector d.frame x w.val))) →
        Nonempty (SecondTraceSectionOutput Y d A G S φ L F hF) := by
  obtain ⟨ηA,CA,hηA,hηA1,hCA,hAssemble⟩ :=
    uniform_actual_second_trace_assembly_with_error_graph hY hΩ hSub hm K ρ c₀ M Cj hK hρ C0 hC0
  obtain ⟨ηB,CB,hηB,hηB1,hCB,hEndpoint⟩ :=
    uniform_actual_frame_covariant_error_endpoints hY hΩ hSub hm K ρ c₀ M Cj hK hρ
  let CE := max CA CB
  have hCE : 0 ≤ CE := hCA.trans (le_max_left _ _)
  refine ⟨min ηA ηB,CE,lt_min hηA hηB,(min_le_left _ _).trans hηA1,hCE,?_⟩
  intro floor hf ε hε hSmall d hd R A hAS hR hA G hGS hG hE
  obtain ⟨S,hSS,hGraph,hSN,hP⟩ := hAssemble floor hf ε hε
    (hSmall.trans (min_le_left _ _)) d hd R A hAS hR hA G hGS hG hE
  have hBounds (y : X) (hy : y ∈ Y) :
      CA*d.radius y*beta d.γ d.radius y ≤ CE*d.radius y*beta d.γ d.radius y ∧
      CB*d.radius y*beta d.γ d.radius y ≤ CE*d.radius y*beta d.γ d.radius y := by
    have hr : 0 ≤ d.radius y := (hd.2.2.2.2.1.2 y hy).1.le
    have hb : 0 ≤ beta d.γ d.radius y := Real.sqrt_nonneg _
    exact ⟨mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_left CA CB) hr) hb,
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_right CA CB) hr) hb⟩
  refine ⟨S,hSS,hGraph,?_,?_,hP⟩
  · intro y hy i j
    exact (hSN y hy i j).trans (hBounds y hy).1
  · intro y hy i j
    obtain ⟨Lo,Hi,hLo,hHi,hLN,hHN⟩ := hEndpoint floor hf ε hε
      (hSmall.trans (min_le_right _ _)) d hd R A hAS hR hA G hGS hG y hy i j (S i j y) (hGraph y hy i j)
    exact ⟨Lo,Hi,hLo,hHi,hLN.trans (hBounds y hy).2,hHN.trans (hBounds y hy).2⟩
end ShrinkingSpheres
