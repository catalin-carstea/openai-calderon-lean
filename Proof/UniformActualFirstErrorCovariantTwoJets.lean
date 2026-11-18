import Proof.UniformActualFirstErrorSecondCovariant
import Proof.UniformActualFirstErrorSmoothCovariant

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2800000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
open Set
open scoped ContDiff Topology InnerProductSpace
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.SphereHarmonic

/-- One globally smooth first covariant derivative is fixed before all
centers and tests; its genuine second covariant graphs have a common
radius-beta-squared bound for arbitrary admitted profiles and frames. -/
theorem uniform_actual_first_error_covariant_two_jets {Y Ω : Set X}
    (hY : IsOpen Y) (hΩ : IsOpen Ω) (hSub : Y ⊆ Ω) {m : ℕ} (hm : 10 ≤ m)
    (K ρ c₀ : ℝ) (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ) (hK : 1 ≤ K) (hρ : 0 < ρ) :
    ∃ η C1 C2 : ℝ,0 < η ∧ η ≤ 1 ∧ 0 ≤ C1 ∧ 0 ≤ C2 ∧
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
      ∃ S : X → X →L[ℝ] (SphereSobolev 1 →L[ℝ] SphereSobolev 0),
        ContDiffOn ℝ ∞ S Y ∧ ∀ y ∈ Y,
          (∀ b : X,CoarseCovariantRotationGraph d y b (actualFirstAdjointErrorFamily d a A G) (S y b)) ∧
          ‖S y‖ ≤ C1*‖a‖*d.radius y*beta d.γ d.radius y ∧
          ∀ b c : X,‖b‖ ≤ 1 → ‖c‖ ≤ 1 →
            ∃ T : SphereSobolev 1 →L[ℝ] SphereSobolev 0,
              CoarseCovariantRotationGraph d y c (fun x => S x b) T ∧
              ‖T‖ ≤ C2*‖a‖*d.radius y*(beta d.γ d.radius y)^2 := by
  obtain ⟨η1,C1,hη1,hη11,hC1,hFirst⟩ :=
    uniform_actual_first_error_smooth_covariant hY hΩ hSub hm K ρ c₀ M Cj hK hρ
  obtain ⟨η2,C2,hη2,hη21,hC2,hSecond⟩ :=
    uniform_actual_first_error_second_covariant hY hΩ hSub hm K ρ c₀ M Cj hK hρ
  refine ⟨min η1 η2,C1,C2,lt_min hη1 hη2,(min_le_left _ _).trans hη11,hC1,hC2,?_⟩
  intro floor hf ε hε hSmall d hd R A hAS hR hA a G hGS hG
  obtain ⟨S,hSS,hS⟩ := hFirst floor hf ε hε (hSmall.trans (min_le_left _ _)) d hd R A hAS hR hA a G hGS hG
  refine ⟨S,hSS,?_⟩
  intro y hy
  refine ⟨(hS y hy).1,(hS y hy).2,?_⟩
  intro b c hb hc
  exact hSecond floor hf ε hε (hSmall.trans (min_le_right _ _)) d hd R A hR hA a G hG S
    (fun x hx => (hS x hx).1) y hy b c hb hc

end ShrinkingSpheres
