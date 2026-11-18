import Proof.UniformNativeFirstErrorTrueAdjointScaledJets
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
genuine graph and radius-gained actual horizontal three-jets. The degree
commutator is explicit; no adjoint higher regularity is inferred from the
forward higher endpoint. All constants precede admitted profiles. -/
theorem uniform_native_first_error_true_adjoint_higher_three_jets {Y Ω : Set X}
    (hY : IsOpen Y) (hΩ : IsOpen Ω) (hSub : Y ⊆ Ω) {m : ℕ} (hm : 9 ≤ m)
    (K ρ c₀ : ℝ) (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ) (hK : 1 ≤ K) (hρ : 0 < ρ)
    (CQ CI CW CC : ℝ) (hCQ : 0 ≤ CQ) (hCI : 0 ≤ CI) (hCW : 0 ≤ CW) (hCC : 0 ≤ CC)
    (F0 : SmoothCoefficientMatrix 2)
    (hF0 : ∀ z ∈ Metric.closedBall (0:X) 2,coefficientMatrixField 2 F0 z=1) :
    ∃ η C0 C1 : ℝ,0 < η ∧ η ≤ 1 ∧ 0 ≤ C0 ∧ 0 ≤ C1 ∧
      ∀ floor,1 ≤ floor → ∀ ε,0 ≤ ε → ε ≤ η → ∀ d,
      ∀ hd : Admissible Y Ω K ρ c₀ M Cj floor ε d,∀ y ∈ Y,∀ CF CA CM : ℝ,
      ∀ s : NativeRelativeHorizontalTaylorData Y Ω d y F0 CQ CI CW CF CA CM,
      ∃ V : s.response.SymmetricAdjointDomain,∀ a : X,∀ CB : ℝ,
      ∀ C : (j : I) → RelativeCenterErrorCoefficientFamily d y a j CC CB,
        (∀ p ∈ s.centerDegreeDomain V,
          (sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)).comp
            (s.firstErrorTrueAdjointHigherFamily C V hd.1.1 (zero_lt_one.trans_le hK) p)=
          (s.firstAdjointHalfErrorFamily C p).adjoint.comp
            (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num))) ∧
        SmoothFiniteJetBound (s.firstErrorTrueAdjointHigherFamily C V hd.1.1 (zero_lt_one.trans_le hK) ∘
          normalFrameRelativeScaledParameter (beta d.γ d.radius y) y)
          ((0,frameVectorLinear d.frame y),0) 3 (C0*‖a‖*d.radius y) ∧
        ∀ b : ℕ → X,(∀ j,‖b j‖ ≤ 1) → ∀ n : ℕ,n ≤ 3 →
          ‖orderedDirectionalFamily (fun j => normalFrameRelativeHorizontalField d.γ d.radius (b j))
            (s.firstErrorTrueAdjointHigherFamily C V hd.1.1 (zero_lt_one.trans_le hK)) n
            ((y,frameVectorLinear d.frame y),0)‖ ≤ C1*‖a‖*d.radius y*(beta d.γ d.radius y)^n := by
  obtain ⟨η,C0,hη,hη1,hC0,hScaled⟩ := uniform_native_first_error_true_adjoint_higher_scaled_three_jets
    hY hΩ hSub hm K ρ c₀ M Cj hK hρ CQ CI CW CC hCQ hCI hCW hCC F0 hF0
  obtain ⟨CX,hCX,hHorizontal⟩ := uniform_normalFrame_horizontal_from_scaled_three_jets
    hY hΩ hSub (by omega) K M Cj hK
  let C1 := CX*C0
  have hC1 : 0 ≤ C1 := mul_nonneg (zero_le_one.trans hCX) hC0
  refine ⟨η,C0,C1,hη,hη1,hC0,hC1,?_⟩
  intro floor hf ε hε hSmall d hd y hy CF CA CM s
  obtain ⟨V,hV⟩ := hScaled floor hf ε hε hSmall d hd y hy CF CA CM s
  refine ⟨V,?_⟩
  intro a CB C
  have hBound := hV a CB C
  refine ⟨fun p hp => s.firstErrorTrueAdjointHigherFamily_balanced C V hd.1.1
    (zero_lt_one.trans_le hK) hF0 p hp,hBound,?_⟩
  have hH := hHorizontal d hd.1 floor c₀ hf hd.2.2.2.2.1 y hy
    (SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ)) _ (C0*‖a‖*d.radius y) hBound
  intro b hb n hn
  exact (hH b hb n hn).trans_eq (by dsimp only [C1];ring)

end ShrinkingSpheres
