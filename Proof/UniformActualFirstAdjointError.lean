import Proof.ActualFirstAdjointErrorGerm
import Proof.UniformNativeFirstErrorDegreeJets
import Proof.ActualSmoothCenterGradient
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
open OAI.AnisotropicCalderon.DirichletFamily
open OAI.AnisotropicCalderon.SphereHarmonic

/-- Any chosen globally smooth actual radial pair produces the SAME physical
    complete remainder. Its common radius-gained bound follows from genuine
    local packets, with constants before the admitted radius and frame. -/
theorem uniform_actual_smooth_first_adjoint_error {Y Ω : Set X}
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
      ∃ G : X → SphereSobolev 1 →L[ℝ] SphereSobolev 0,
        ContDiffOn ℝ ∞ G Y ∧
        (∀ x ∈ Y,RealizesActualCenterGradientAdjoint d x a (A x) (G x)) ∧
        ContDiffOn ℝ ∞ (actualFirstAdjointErrorFamily d a A G) Y ∧
        ∀ x ∈ Y,‖actualFirstAdjointErrorFamily d a A G x‖ ≤ CE*‖a‖*d.radius x := by
  classical
  obtain ⟨ηT,CF,CA,CM,CQ,CI,CW,F0,hηT,hηT1,hCF,hCA,hCM,hCQ,hCI,hCW,hF0,hNative⟩ :=
    uniform_native_relative_horizontal_taylor_data hY hΩ hSub (by omega) K ρ c₀ M Cj hK hρ
  obtain ⟨ηC,CC,CH,hηC,hηC1,hCC,hCH,hC⟩ :=
    uniform_relative_center_error_coefficient_families hY hΩ hSub hm K ρ c₀ M Cj hK hρ
  obtain ⟨ηE,CE,CD,CDH,hηE,hηE1,hCE,hCD,hCDH,hError⟩ :=
    uniform_native_first_error_degree_three_jets hY hΩ hSub (by omega) K ρ c₀ M Cj hK hρ
      CQ CI CW CC (zero_le_one.trans hCQ) hCI hCW (zero_le_one.trans hCC) F0 hF0
  refine ⟨min ηT (min ηC ηE),CE,lt_min hηT (lt_min hηC hηE),
    (min_le_left _ _).trans hηT1,hCE,?_⟩
  intro floor hf ε hε hSmall d hd R A hAS hR hA a
  have hSmallT := hSmall.trans (min_le_left _ _)
  have hSmallC := hSmall.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hSmallE := hSmall.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hCf := fun y hy j => hC floor hf ε hε hSmallC d hd y hy a j
  obtain ⟨G,hGS,hG⟩ := exists_smooth_actual_center_gradient_adjoint hY
    (fun x hx => (hd.2.2.2.2.1.2 x hx).1.ne') hd.2.2.2.2.1.1
    (fun i => (hd.1.2.2.2.2.2.2.1 i).mono hSub) hCf A hAS
  refine ⟨G,hGS,hG,contDiffOn_actualFirstAdjointErrorFamily a hY hΩ hSub hd.1
    (zero_lt_one.trans_le hK) hd.2.2.2.2.1.1 (fun x hx => (hd.2.2.2.2.1.2 x hx).1) A G hAS hGS,?_⟩
  intro y hy
  obtain ⟨s⟩ := hNative floor hf ε hε hSmallT d hd y hy
  obtain ⟨V,hJets⟩ := hError floor hf ε hε hSmallE d hd y hy CF CA CM s
  let C : (j : I) → RelativeCenterErrorCoefficientFamily d y a j CC CH :=
    fun j => Classical.choice (hCf y hy j)
  have hGerm := s.actual_first_adjoint_error_germ V hY hΩ hSub hd.1 (zero_lt_one.trans_le hK)
    hy (hd.2.2.2.2.1.2 y hy).1.ne' hd.2.2.2.2.1.1 C R A G hR hA hG
  have hPoint := hGerm.eq_of_nhds
  rw [normalFrameRelativeActualParameter_point d y (hd.2.2.2.2.1.2 y hy).1.ne'] at hPoint
  have hFields := (hJets a CH C).1
  have hBound := hFields.operator.bound 0 (by omega)
  rw [norm_iteratedFDeriv_zero] at hBound
  change ‖(s.firstErrorAngularFields C (normalFrameRelativeScaledParameter (beta d.γ d.radius y) y
    ((0,frameVectorLinear d.frame y),0))).operator‖ ≤ _ at hBound
  rw [normalFrameRelativeScaledParameter_point,s.firstErrorAngularFields_operator] at hBound
  rw [hPoint]
  exact hBound
end ShrinkingSpheres
