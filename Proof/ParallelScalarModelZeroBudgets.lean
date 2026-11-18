import Proof.ParallelScalarModelZeroWeights

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2800000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
open Set
open scoped ContDiff Topology
namespace ShrinkingSpheres.ParallelEnergy

structure ScalarModelZeroWeightBudget (Y Ω : Set X) (m : ℕ) (K ρ c₀ : ℝ)
    (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ) where
  zeroBound : ℝ
  firstBound : ℝ
  zero_nonneg : 0 ≤ zeroBound
  first_nonneg : 0 ≤ firstBound
  actual : ∀ floor,1 ≤ floor → ∀ ε,0 ≤ ε → ε ≤ 1 → ∀ d,
    Admissible Y Ω K ρ c₀ M Cj floor ε d → ∀ a b k c : I,
    ContDiffOn ℝ ∞ (scalarModelZeroDensityWeight d a b k c) Y ∧ ∀ y ∈ Y,∀ i : I,
      |scalarModelZeroDensityWeight d a b k c y| ≤ zeroBound*ε/beta d.γ d.radius y*metricDensity d.γ y ∧
      |fderiv ℝ (scalarModelZeroDensityWeight d a b k c) y (axis i)| ≤ firstBound*ε*metricDensity d.γ y

theorem scalar_model_zero_weight_budget_exists {Y Ω : Set X}
    (hY : IsOpen Y) (hΩ : IsOpen Ω) (hSub : Y ⊆ Ω) {m : ℕ} (hm : 2 ≤ m)
    (K ρ c₀ : ℝ) (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ) (hK : 1 ≤ K) :
    Nonempty (ScalarModelZeroWeightBudget Y Ω m K ρ c₀ M Cj) := by
  obtain ⟨Z0,Z1,hZ0,hZ1,hActual⟩ := uniform_scalar_model_zero_density_weight_jets hY hΩ hSub hm K ρ c₀ M Cj hK
  exact ⟨⟨Z0,Z1,hZ0,hZ1,hActual⟩⟩

end ShrinkingSpheres.ParallelEnergy
