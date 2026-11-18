import Proof.NativeActualFirstErrorCovariant
import Proof.UniformNativeFirstErrorDegreeJets
import Proof.UniformNativeRelativeHorizontalTaylorData
import Proof.RelativeCenterErrorCoefficientFamily
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3800000
set_option maxSynthPendingDepth 30
set_option maxRecDepth 2200
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
open Set Filter
open scoped ContDiff Topology InnerProductSpace
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.DirichletFamily OAI.AnisotropicCalderon.SphereHarmonic

theorem uniform_actual_first_error_covariant {Y Ω : Set X}
    (hY : IsOpen Y) (hΩ : IsOpen Ω) (hSub : Y ⊆ Ω) {m : ℕ} (hm : 10 ≤ m)
    (K ρ c₀ : ℝ) (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ) (hK : 1 ≤ K) (hρ : 0 < ρ) :
    ∃ η CE : ℝ,0 < η ∧ η ≤ 1 ∧ 0 ≤ CE ∧
      ∀ floor,1 ≤ floor → ∀ ε,0 ≤ ε → ε ≤ η → ∀ d,
      Admissible Y Ω K ρ c₀ M Cj floor ε d →
      ∀ R A : X → SphereSobolev 1 →L[ℝ] SphereSobolev 0,
      ContDiffOn ℝ ∞ A Y →
      (∀ x ∈ Y,RealizesActualMidpointRadialError d x (R x)) →
      (∀ x ∈ Y,∀ u v,⟪(R x+sphereSobolevDegreeL) u,sphereSobolevInclusionL 1 0 (by norm_num) v⟫_ℝ =
        ⟪sphereSobolevInclusionL 1 0 (by norm_num) u,A x v⟫_ℝ) → ∀ a : X,
      ∀ G : X → SphereSobolev 1 →L[ℝ] SphereSobolev 0,
      ContDiffOn ℝ ∞ G Y →
      (∀ x ∈ Y,RealizesActualCenterGradientAdjoint d x a (A x) (G x)) →
      ∀ y ∈ Y,∀ b : X,‖b‖ ≤ 1 →
      ∃ S : SphereSobolev 1 →L[ℝ] SphereSobolev 0,
        CoarseCovariantRotationGraph d y b (actualFirstAdjointErrorFamily d a A G) S ∧
        ‖S‖ ≤ CE*‖a‖*d.radius y*beta d.γ d.radius y := by
  classical
  obtain ⟨ηT,CF,CA,CM,CQ,CI,CW,F0,hηT,hηT1,hCF,hCA,hCM,hCQ,hCI,hCW,hF0,hNative⟩ :=
    uniform_native_relative_horizontal_taylor_data hY hΩ hSub (by omega) K ρ c₀ M Cj hK hρ
  obtain ⟨ηC,CC,CH,hηC,hηC1,hCC,hCH,hC⟩ :=
    uniform_relative_center_error_coefficient_families hY hΩ hSub hm K ρ c₀ M Cj hK hρ
  obtain ⟨ηE,CE,CD,CDH,hηE,hηE1,hCE,hCD,hCDH,hError⟩ :=
    uniform_native_first_error_degree_three_jets hY hΩ hSub (by omega) K ρ c₀ M Cj hK hρ
      CQ CI CW CC (zero_le_one.trans hCQ) hCI hCW (zero_le_one.trans hCC) F0 hF0
  obtain ⟨CX,hCX,hHorizontal⟩ := uniform_normalFrame_horizontal_from_scaled_three_jets hY hΩ hSub (by omega) K M Cj hK
  refine ⟨min ηT (min ηC ηE),CX*CE,lt_min hηT (lt_min hηC hηE),
    (min_le_left _ _).trans hηT1,mul_nonneg (zero_le_one.trans hCX) hCE,?_⟩
  intro floor hf ε hε hSmall d hd R A hAS hR hA a G hGS hG y hy b hb
  have hSmallT := hSmall.trans (min_le_left _ _)
  have hSmallC := hSmall.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hSmallE := hSmall.trans ((min_le_right _ _).trans (min_le_right _ _))
  obtain ⟨s⟩ := hNative floor hf ε hε hSmallT d hd y hy
  obtain ⟨V,hJets⟩ := hError floor hf ε hε hSmallE d hd y hy CF CA CM s
  let C : (j : I) → RelativeCenterErrorCoefficientFamily d y a j CC CH :=
    fun j => Classical.choice (hC floor hf ε hε hSmallC d hd y hy a j)
  let F := s.firstAdjointErrorFamily C
  let p : NormalFrameRelativeParameter := ((y,frameVectorLinear d.frame y),0)
  let S := fderiv ℝ F p (normalFrameRelativeHorizontalField d.γ d.radius b p)
  refine ⟨S,s.actual_first_error_covariant_graph C V hY hΩ hSub hd (zero_lt_one.trans_le hK) hy
    R A G hAS hGS hR hA hG b,?_⟩
  have hFields := (hJets a CH C).1
  have hBound := hFields.operator
  have hFam : (fun q => (s.firstErrorAngularFields C
      (normalFrameRelativeScaledParameter (beta d.γ d.radius y) y q)).operator)=
      F ∘ normalFrameRelativeScaledParameter (beta d.γ d.radius y) y := by
    funext q
    exact s.firstErrorAngularFields_operator C _
  change SmoothFiniteJetBound (fun q => (s.firstErrorAngularFields C
    (normalFrameRelativeScaledParameter (beta d.γ d.radius y) y q)).operator) _ 3 _ at hBound
  rw [hFam] at hBound
  have hh := hHorizontal d hd.1 floor c₀ hf hd.2.2.2.2.1 y hy
    (SphereSobolev 1 →L[ℝ] SphereSobolev 0) F (CE*‖a‖*d.radius y) hBound
    (fun _ => b) (fun _ => hb) 1 (by norm_num)
  simpa only [orderedDirectionalFamily,pow_one,S,p,mul_assoc] using hh
end ShrinkingSpheres
