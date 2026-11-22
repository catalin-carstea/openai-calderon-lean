module

public import Proof.CalderonN.ActualPerturbationCoercivity

import Proof.CalderonN.SmoothFlatConormalResponse
import Mathlib.Tactic

/-! The manuscript's perturbation estimate suffices for the public
coercivity statement with the actual model and lower-order terms. -/

public section

noncomputable section
open Set Metric
open scoped ContDiff Matrix.Norms.Elementwise
set_option autoImplicit false
set_option maxHeartbeats 3700000
set_option backward.isDefEq.respectTransparency false
namespace CalderonN

open BallDirichlet TauCeti PDE
variable {dim : ℕ} [NeZero dim] [Nontrivial (Fin dim)]

@[expose] def UniformActualMovingTracePrincipalError (hn : 3 ≤ dim) : Prop :=
  ∀ (Y Ω : Set (X dim)) (hY : IsOpen Y), IsOpen Ω → IsCompact (closure Y) → closure Y ⊆ Ω →
    ∃ m : ℕ,8 ≤ m ∧ ∀ (K ρ c₀ : ℝ) (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ)
      (hK : 1 ≤ K),0 < ρ → 0 < c₀ →
      ∀ (S : ∀ f : SmoothData dim,ConormalTaylorSolutions (fun _ => (1:Mat dim)) 0 f),
        ∃ η C : ℝ,0 < η ∧ 0 ≤ C ∧ ∀ floor ≥ 1,∀ ε,0 ≤ ε → ε ≤ η → ∀ d,
          Admissible Y Ω K ρ c₀ M Cj floor ε d →
          (∀ x i,d.frame x i = smoothMetricFrame (d.γ x) i) →
          ActualMovingTracePrincipalErrorEstimate hn hY (zero_lt_one.trans_le hK) contDiff_const
            (uniformlyEllipticOn_const_one_one (n:=Fin dim) (fixedBallOpens dim : Set (X dim))) S d ε C

theorem coercivity_of_uniformActualMovingTracePrincipalError (hn : 3 ≤ dim) (h : UniformActualMovingTracePrincipalError hn) :
    Coercivity dim := by
  intro Y Ω hY hΩ hYc hYΩ
  have hSub : Y ⊆ Ω := subset_closure.trans hYΩ
  obtain ⟨F,hF⟩ := exists_flatCoefficientMatrix dim 2
  have hS (f : SmoothData dim) :
      Nonempty (ConormalTaylorSolutions (fun _ => (1:Mat dim)) 0 f) := by
    obtain ⟨u,q,hu,hu',hq,hq'⟩ := exists_smooth_flat_response_and_variation F hF 0 f
    exact ⟨⟨u,u,q,hu,hu',hu,hu',hq,hq'⟩⟩
  let S (f : SmoothData dim) := Classical.choice (hS f)
  obtain ⟨m,hm,hE⟩ := h Y Ω hY hΩ hYc hYΩ
  refine ⟨m,?_⟩
  intro K ρ c₀ M Cj hK hρ hc₀
  obtain ⟨η,C,hη,hC,hBound⟩ := hE K ρ c₀ M Cj hK hρ hc₀ S
  exact uniformEstimate_of_actualMovingTracePrincipalError hn hY hΩ hYc hSub hm K ρ c₀ M Cj hK hρ hc₀
    contDiff_const (uniformlyEllipticOn_const_one_one (n:=Fin dim) (fixedBallOpens dim : Set (X dim)))
    S hη hC hBound

end CalderonN
