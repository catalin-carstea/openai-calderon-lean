import Proof.ParallelScalarModelWeights
import Proof.FramedRaisingStrongHalfJet

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2800000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
open Set
open scoped ContDiff Topology
namespace ShrinkingSpheres.ParallelEnergy

structure ScalarModelRaisingBudget (Y Ω : Set X) (m : ℕ) (K ρ c₀ : ℝ)
    (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ) where
  bound : ℝ
  nonneg : 0 ≤ bound
  actual : ∀ floor ε : ℝ,∀ d,Admissible Y Ω K ρ c₀ M Cj floor ε d →
    ∀ y ∈ Y,∀ i b : I,‖framedRaisingHalfL d y (axis b)‖ ≤ bound ∧
      ‖framedRaisingFirstHalfJet d i b y‖ ≤ bound

theorem scalar_model_raising_budget_exists {Y Ω : Set X}
    (hY : IsOpen Y) (hΩ : IsOpen Ω) {m : ℕ} (hm : 1 ≤ m)
    (K ρ c₀ : ℝ) (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ) (hK : 1 ≤ K) :
    Nonempty (ScalarModelRaisingBudget Y Ω m K ρ c₀ M Cj) := by
  obtain ⟨Q,hQ,hActual⟩ := @uniform_framed_raising_strong_half_one_jet Y Ω hY hΩ m hm K ρ c₀ M Cj hK
  exact ⟨⟨Q,hQ,hActual⟩⟩

structure ScalarModelLeadingWeightBudget (Y Ω : Set X) (m : ℕ) (K ρ c₀ : ℝ)
    (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ) where
  zeroBound : ℝ
  firstBound : ℝ
  zero_nonneg : 0 ≤ zeroBound
  first_nonneg : 0 ≤ firstBound
  actual : ∀ floor,1 ≤ floor → ∀ ε,0 ≤ ε → ε ≤ 1 → ∀ d,
    Admissible Y Ω K ρ c₀ M Cj floor ε d → ∀ a b k c : I,
    ContDiffOn ℝ ∞ (scalarModelLeadingWeight d a b k c) Y ∧ ∀ y ∈ Y,∀ i : I,
      |scalarModelLeadingWeight d a b k c y| ≤ zeroBound*ε/(beta d.γ d.radius y)^2 ∧
      |fderiv ℝ (scalarModelLeadingWeight d a b k c) y (axis i)| ≤ firstBound*ε/beta d.γ d.radius y

theorem scalar_model_leading_weight_budget_exists {Y Ω : Set X}
    (hY : IsOpen Y) (hΩ : IsOpen Ω) (hSub : Y ⊆ Ω) {m : ℕ} (hm : 2 ≤ m)
    (K ρ c₀ : ℝ) (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ) (hK : 1 ≤ K) :
    Nonempty (ScalarModelLeadingWeightBudget Y Ω m K ρ c₀ M Cj) := by
  obtain ⟨A0,A1,hA0,hA1,hActual⟩ := uniform_scalar_model_leading_weight_jets hY hΩ hSub hm K ρ c₀ M Cj hK
  exact ⟨⟨A0,A1,hA0,hA1,hActual⟩⟩

end ShrinkingSpheres.ParallelEnergy
