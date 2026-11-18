import Proof.ParallelFirstSelfNativeAdjointPacket
import Proof.UniformNativeFirstErrorTrueAdjointHigherJets

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

/-- One native true-adjoint HIGH family with its graph, scaled three-jets,
and actual horizontal three-jets. The same domain and center witnesses
are retained for later first and second physical transfer. -/
structure FirstSelfNativeAdjointThreeJetPacket
    (Y Ω : Set X) (d : Data) (y a : X) (K C0 C1 : ℝ) where
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
  elliptic : Elliptic Ω K d.γ
  positive : 0 < K
  graph : ∀ p ∈ native.centerDegreeDomain domain,
    (sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)).comp
      (native.firstErrorTrueAdjointHigherFamily coefficients domain elliptic positive p)=
      (native.firstAdjointHalfErrorFamily coefficients p).adjoint.comp
        (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num))
  scaled : SmoothFiniteJetBound
    (native.firstErrorTrueAdjointHigherFamily coefficients domain elliptic positive ∘
      normalFrameRelativeScaledParameter (beta d.γ d.radius y) y)
    ((0,frameVectorLinear d.frame y),0) 3 (C0*‖a‖*d.radius y)
  horizontal : ∀ b : ℕ → X,(∀ j,‖b j‖ ≤ 1) → ∀ n : ℕ,n ≤ 3 →
    ‖orderedDirectionalFamily (fun j => normalFrameRelativeHorizontalField d.γ d.radius (b j))
      (native.firstErrorTrueAdjointHigherFamily coefficients domain elliptic positive) n
      ((y,frameVectorLinear d.frame y),0)‖ ≤ C1*‖a‖*d.radius y*(beta d.γ d.radius y)^n

/-- Full native HIGH adjoint jets are selected once before physical
endpoints or tests. This strengthens the preserved packet, not the premises. -/
theorem uniform_first_self_native_adjoint_three_jet_packet
    {Y Ω : Set X} (hY : IsOpen Y) (hΩ : IsOpen Ω) (hSub : Y ⊆ Ω)
    {m : ℕ} (hm : 10 ≤ m) (K ρ c₀ : ℝ) (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ)
    (hK : 1 ≤ K) (hρ : 0 < ρ) :
    ∃ η C0 C1 : ℝ,0 < η ∧ η ≤ 1 ∧ 0 ≤ C0 ∧ 0 ≤ C1 ∧
      ∀ floor,1 ≤ floor → ∀ ε,0 ≤ ε → ε ≤ η → ∀ d,
      Admissible Y Ω K ρ c₀ M Cj floor ε d → ∀ y ∈ Y,∀ a : X,
      Nonempty (FirstSelfNativeAdjointThreeJetPacket Y Ω d y a K C0 C1) := by
  obtain ⟨ηT,CF,CA,CM,CQ,CI,CW,F0,hηT,hηT1,hCF,hCA,hCM,hCQ,hCI,hCW,hF0,hNative⟩ :=
    uniform_native_relative_horizontal_taylor_data hY hΩ hSub (by omega) K ρ c₀ M Cj hK hρ
  obtain ⟨ηC,CC,CH,hηC,hηC1,hCC,hCH,hCoeff⟩ :=
    uniform_relative_center_error_coefficient_families hY hΩ hSub hm K ρ c₀ M Cj hK hρ
  obtain ⟨ηE,C0,C1,hηE,hηE1,hC0,hC1,hEndpoint⟩ :=
    uniform_native_first_error_true_adjoint_higher_three_jets hY hΩ hSub (by omega) K ρ c₀ M Cj hK hρ
      CQ CI CW CC (zero_le_one.trans hCQ) hCI hCW (zero_le_one.trans hCC) F0 hF0
  refine ⟨min ηT (min ηC ηE),C0,C1,lt_min hηT (lt_min hηC hηE),
    (min_le_left _ _).trans hηT1,hC0,hC1,?_⟩
  intro floor hf ε hε hSmall d hd y hy a
  obtain ⟨s⟩ := hNative floor hf ε hε (hSmall.trans (min_le_left _ _)) d hd y hy
  obtain ⟨V,hEnd⟩ := hEndpoint floor hf ε hε
    (hSmall.trans ((min_le_right _ _).trans (min_le_right _ _))) d hd y hy CF CA CM s
  let C : (j : I) → RelativeCenterErrorCoefficientFamily d y a j CC CH :=
    fun j => Classical.choice (hCoeff floor hf ε hε
      (hSmall.trans ((min_le_right _ _).trans (min_le_left _ _))) d hd y hy a j)
  have hAll := hEnd a CH C
  exact ⟨⟨F0,CQ,CI,CW,CF,CA,CM,CC,CH,s,V,C,hF0,hd.1.1,zero_lt_one.trans_le hK,
    hAll.1,hAll.2.1,hAll.2.2⟩⟩

end ShrinkingSpheres.ParallelEnergy
