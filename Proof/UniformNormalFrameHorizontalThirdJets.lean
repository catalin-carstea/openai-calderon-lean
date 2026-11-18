import Proof.UniformNormalFrameScaledHorizontalJets

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3600000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter
open scoped ContDiff Topology
namespace ShrinkingSpheres

/-- Every same-family joint quadratic three-jet gives actual repeated
    horizontal jets with exactly beta per derivative, for arbitrary profiles
    and frames. All constants precede the data and the operator family. -/
theorem uniform_normalFrame_horizontal_third_jets {Y Ω : Set X}
    (hY : IsOpen Y) (hΩ : IsOpen Ω) (hSub : Y ⊆ Ω) {m : ℕ} (hm : 3 ≤ m)
    (K : ℝ) (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ) (hK : 1 ≤ K) :
    ∃ CH : ℝ,1 ≤ CH ∧ ∀ d : Data,Background Ω K M d.γ d.g₁ d.g₂ d.frame →
      ∀ floor c₀,1 ≤ floor → Profile Y d.γ d.frame d.radius floor c₀ Cj → ∀ y ∈ Y,
      ∀ (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E],
      ∀ F : NormalFrameRelativeParameter → E,ContDiffAt ℝ ∞ F ((y,frameVectorLinear d.frame y),0) →
      ∀ C r : ℝ,0 ≤ C →
      (∀ j : ℕ,j ≤ 3 → ‖iteratedFDeriv ℝ j F ((y,frameVectorLinear d.frame y),0)‖ ≤ C*r^2) →
      ∀ a : ℕ → X,(∀ j,‖a j‖ ≤ 1) → ∀ n : ℕ,n ≤ 3 →
      ‖orderedDirectionalFamily (fun j => normalFrameRelativeHorizontalField d.γ d.radius (a j)) F n
        ((y,frameVectorLinear d.frame y),0)‖ ≤ CH*C*r^2*(beta d.γ d.radius y)^n := by
  obtain ⟨CH,hCH,hHorizontal⟩ := uniform_normalFrame_horizontal_from_scaled_three_jets hY hΩ hSub hm K M Cj hK
  refine ⟨6*CH,by linarith only [hCH],?_⟩
  intro d hd floor c₀ hf hp y hy E _ _ F hF C r hC hFJets a ha n hn
  have hβ : 1 ≤ beta d.γ d.radius y := hf.trans (hp.2 y hy).2.1
  have hFBound : SmoothFiniteJetBound F ((y,frameVectorLinear d.frame y),0) 3 (C*r^2) := ⟨by positivity,hF,hFJets⟩
  have hFs := normalFrame_scaled_parameter_three_jet_bound (beta d.γ d.radius y) hβ y (frameVectorLinear d.frame y) hFBound
  have hh := hHorizontal d hd floor c₀ hf hp y hy E F (6*(C*r^2)) hFs a ha n hn
  exact hh.trans_eq (by ring)

end ShrinkingSpheres
