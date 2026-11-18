import Proof.NormalFrameScaledJetBounds
import Proof.UniformNormalFrameScaledFiniteJets
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxSynthPendingDepth 30
set_option maxRecDepth 2000
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
open Set Filter
open scoped ContDiff Topology
namespace ShrinkingSpheres

/-- An actual family estimated in beta-rescaled parameters has uniform true
    horizontal three-jets, without any derivative budget for the chosen frame. -/
theorem uniform_normalFrame_horizontal_from_scaled_three_jets {Y Ω : Set X}
    (hY : IsOpen Y) (hΩ : IsOpen Ω) (hSub : Y ⊆ Ω) {m : ℕ} (hm : 3 ≤ m)
    (K : ℝ) (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ) (hK : 1 ≤ K) :
    ∃ CH : ℝ,1 ≤ CH ∧ ∀ d : Data,Background Ω K M d.γ d.g₁ d.g₂ d.frame →
      ∀ floor c₀,1 ≤ floor → Profile Y d.γ d.frame d.radius floor c₀ Cj → ∀ y ∈ Y,
      ∀ (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E],
      ∀ (F : NormalFrameRelativeParameter → E) (B : ℝ),
      SmoothFiniteJetBound (F ∘ normalFrameRelativeScaledParameter (beta d.γ d.radius y) y)
        ((0,frameVectorLinear d.frame y),0) 3 B →
      ∀ a : ℕ → X,(∀ j,‖a j‖ ≤ 1) → ∀ n : ℕ,n ≤ 3 →
      ‖orderedDirectionalFamily (fun j => normalFrameRelativeHorizontalField d.γ d.radius (a j)) F n
        ((y,frameVectorLinear d.frame y),0)‖ ≤ CH*B*(beta d.γ d.radius y)^n := by
  exact uniform_normalFrame_horizontal_from_scaled_finite_jets 3 le_rfl hY hΩ hSub hm K M Cj hK
end ShrinkingSpheres
