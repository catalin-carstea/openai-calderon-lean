import Proof.NativeFirstErrorTrueAdjointHigher
import Proof.UniformNativeFirstAdjointErrorEndpoints
import Proof.UniformNativeFirstErrorDegreeJets

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2800000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
open Set
open scoped ContDiff Topology
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.DirichletFamily OAI.AnisotropicCalderon.SphereHarmonic

/-- The SAME native first error has a true-adjoint higher family with
radius-gained rescaled three-jets. The degree
commutator is explicit; no adjoint higher regularity is inferred from the
forward higher endpoint. All constants precede admitted profiles. -/
theorem uniform_native_first_error_true_adjoint_higher_scaled_three_jets {Y Ω : Set X}
    (hY : IsOpen Y) (hΩ : IsOpen Ω) (hSub : Y ⊆ Ω) {m : ℕ} (hm : 9 ≤ m)
    (K ρ c₀ : ℝ) (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ) (hK : 1 ≤ K) (hρ : 0 < ρ)
    (CQ CI CW CC : ℝ) (hCQ : 0 ≤ CQ) (hCI : 0 ≤ CI) (hCW : 0 ≤ CW) (hCC : 0 ≤ CC)
    (F0 : SmoothCoefficientMatrix 2)
    (hF0 : ∀ z ∈ Metric.closedBall (0:X) 2,coefficientMatrixField 2 F0 z=1) :
    ∃ η C0 : ℝ,0 < η ∧ η ≤ 1 ∧ 0 ≤ C0 ∧
      ∀ floor,1 ≤ floor → ∀ ε,0 ≤ ε → ε ≤ η → ∀ d,
      ∀ hd : Admissible Y Ω K ρ c₀ M Cj floor ε d,∀ y ∈ Y,∀ CF CA CM : ℝ,
      ∀ s : NativeRelativeHorizontalTaylorData Y Ω d y F0 CQ CI CW CF CA CM,
      ∃ V : s.response.SymmetricAdjointDomain,∀ a : X,∀ CB : ℝ,
      ∀ C : (j : I) → RelativeCenterErrorCoefficientFamily d y a j CC CB,
        SmoothFiniteJetBound (s.firstErrorTrueAdjointHigherFamily C V hd.1.1 (zero_lt_one.trans_le hK) ∘
          normalFrameRelativeScaledParameter (beta d.γ d.radius y) y)
          ((0,frameVectorLinear d.frame y),0) 3 (C0*‖a‖*d.radius y) := by
  obtain ⟨ηE,CE,CEH,hηE,hηE1,hCE,hCEH,hEndpoint⟩ := uniform_native_first_adjoint_error_endpoints
    hY hΩ hSub hm K ρ c₀ M Cj hK hρ CQ CI CW CC hCQ hCI hCW hCC F0 hF0
  obtain ⟨ηD,CAng,CD,CDH,hηD,hηD1,hCAng,hCD,hCDH,hDegree⟩ := uniform_native_first_error_degree_three_jets
    hY hΩ hSub hm K ρ c₀ M Cj hK hρ CQ CI CW CC hCQ hCI hCW hCC F0 hF0
  let C0 := CE+CD
  have hC0 : 0 ≤ C0 := add_nonneg hCE hCD
  refine ⟨min ηE ηD,C0,lt_min hηE hηD,(min_le_left _ _).trans hηE1,hC0,?_⟩
  intro floor hf ε hε hSmall d hd y hy CF CA CM s
  obtain ⟨Vt,Vc,hE⟩ := hEndpoint floor hf ε hε (hSmall.trans (min_le_left _ _)) d hd y hy CF CA CM s
  obtain ⟨V,hD⟩ := hDegree floor hf ε hε (hSmall.trans (min_le_right _ _)) d hd y hy CF CA CM s
  refine ⟨V,?_⟩
  intro a CB C
  have hRaw := halfDegreeAdjointHigherLift_jet_bound (hE a CB C).1 (hD a CB C).2.1
  have hBound : SmoothFiniteJetBound
      (s.firstErrorTrueAdjointHigherFamily C V hd.1.1 (zero_lt_one.trans_le hK) ∘
        normalFrameRelativeScaledParameter (beta d.γ d.radius y) y)
      ((0,frameVectorLinear d.frame y),0) 3 (C0*‖a‖*d.radius y) := by
    have hSum : CE*‖a‖*d.radius y+CD*‖a‖*d.radius y=C0*‖a‖*d.radius y := by
      dsimp only [C0]
      ring
    rw [hSum] at hRaw
    exact hRaw
  exact hBound

end ShrinkingSpheres
