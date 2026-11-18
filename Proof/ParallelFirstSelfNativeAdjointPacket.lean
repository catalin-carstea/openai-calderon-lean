import Proof.UniformNativeTrueAdjointHorizontalJet
import Proof.RelativeCenterErrorCoefficientFamily

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2800000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
open Set
open scoped ContDiff Topology
namespace ShrinkingSpheres.ParallelEnergy
open OAI.AnisotropicCalderon.DirichletFamily OAI.AnisotropicCalderon.SphereHarmonic

/-- Native witnesses and their actual differentiated true-adjoint graph,
selected together before a physical operator or test is supplied. -/
structure FirstSelfNativeAdjointPacket (Y Ω : Set X) (d : Data) (y a : X) (CE ε : ℝ) where
  F0 : SmoothCoefficientMatrix 2
  CQ : ℝ
  CI : ℝ
  CW : ℝ
  CF : ℝ
  CA : ℝ
  CM : ℝ
  CC : ℝ
  CH : ℝ
  native : NativeRelativeHorizontalTaylorData Y Ω d y F0 CQ CI CW CF CA CM
  domain : native.response.SymmetricAdjointDomain
  coefficients : (j : I) → RelativeCenterErrorCoefficientFamily d y a j CC CH
  flat : ∀ z ∈ Metric.closedBall (0:X) 2,coefficientMatrixField 2 F0 z=1
  jet : ∀ b : X,‖b‖ ≤ 1 →
    ∃ H : SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ),
      (sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)).comp H=
        (fderiv ℝ (fun q => (native.firstAdjointHalfErrorFamily coefficients q).adjoint)
          ((y,frameVectorLinear d.frame y),0)
          (normalFrameRelativeHorizontalField d.γ d.radius b ((y,frameVectorLinear d.frame y),0))).comp
            (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)) ∧
      ‖H‖ ≤ CE*‖a‖*d.radius y*beta d.γ d.radius y ∧ ‖H‖ ≤ CE*‖a‖*ε

/-- Uniform native witness selection is kept separate from physical transport. -/
theorem uniform_first_self_native_adjoint_packet
    {Y Ω : Set X} (hY : IsOpen Y) (hΩ : IsOpen Ω) (hSub : Y ⊆ Ω)
    {m : ℕ} (hm : 10 ≤ m) (K ρ c₀ : ℝ) (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ)
    (hK : 1 ≤ K) (hρ : 0 < ρ) :
    ∃ η CE : ℝ,0 < η ∧ η ≤ 1 ∧ 0 ≤ CE ∧
      ∀ floor,1 ≤ floor → ∀ ε,0 ≤ ε → ε ≤ η → ∀ d,
      Admissible Y Ω K ρ c₀ M Cj floor ε d → ∀ y ∈ Y,∀ a : X,
      Nonempty (FirstSelfNativeAdjointPacket Y Ω d y a CE ε) := by
  obtain ⟨ηT,CF,CA,CM,CQ,CI,CW,F0,hηT,hηT1,hCF,hCA,hCM,hCQ,hCI,hCW,hF0,hNative⟩ :=
    uniform_native_relative_horizontal_taylor_data hY hΩ hSub (by omega) K ρ c₀ M Cj hK hρ
  obtain ⟨ηC,CC,CH,hηC,hηC1,hCC,hCH,hCoeff⟩ :=
    uniform_relative_center_error_coefficient_families hY hΩ hSub hm K ρ c₀ M Cj hK hρ
  obtain ⟨ηE,CE,hηE,hηE1,hCE,hEndpoint⟩ :=
    uniform_native_first_error_true_adjoint_horizontal_higher_jet hY hΩ hSub (by omega) K ρ c₀ M Cj hK hρ
      CQ CI CW CC (zero_le_one.trans hCQ) hCI hCW (zero_le_one.trans hCC) F0 hF0
  refine ⟨min ηT (min ηC ηE),CE,lt_min hηT (lt_min hηC hηE),
    (min_le_left _ _).trans hηT1,hCE,?_⟩
  intro floor hf ε hε hSmall d hd y hy a
  obtain ⟨s⟩ := hNative floor hf ε hε (hSmall.trans (min_le_left _ _)) d hd y hy
  obtain ⟨V,hEnd⟩ := hEndpoint floor hf ε hε
    (hSmall.trans ((min_le_right _ _).trans (min_le_right _ _))) d hd y hy CF CA CM s
  let C : (j : I) → RelativeCenterErrorCoefficientFamily d y a j CC CH :=
    fun j => Classical.choice (hCoeff floor hf ε hε
      (hSmall.trans ((min_le_right _ _).trans (min_le_left _ _))) d hd y hy a j)
  exact ⟨⟨F0,CQ,CI,CW,CF,CA,CM,CC,CH,s,V,C,hF0,hEnd a CH C⟩⟩

end ShrinkingSpheres.ParallelEnergy
