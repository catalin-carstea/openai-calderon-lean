module

public import Proof.CalderonN.CurvatureOperatorBounds

import Mathlib.Tactic

@[expose] public section

noncomputable section
set_option autoImplicit false
open Set
namespace CalderonN
variable {n : ℕ}

def curvatureBudget (n : ℕ) (K M₀ M₁ M₂ : ℝ) : ℝ :=
  2*(n:ℝ)^2*M₀*((n:ℝ)^3*(3*(n:ℝ)^3*K^2*M₁^2+3*(n:ℝ)*K*M₂)+((n:ℝ)^3*(3*(n:ℝ)*K*M₁))^2)*K^2

lemma curvatureBudget_nonneg (n : ℕ) (K M₀ M₁ M₂ : ℝ) (hK : 0 ≤ K) (hM₀ : 0 ≤ M₀)
    (hM₁ : 0 ≤ M₁) (hM₂ : 0 ≤ M₂) : 0 ≤ curvatureBudget n K M₀ M₁ M₂ := by
  unfold curvatureBudget
  positivity

/-- A common curvature constant computed from the frozen background budgets through order
    two. Negative unused budgets are replaced by zero, so empty domains cause no exception. -/
def backgroundCurvatureBudget (n : ℕ) {m : ℕ} (hm : 2 ≤ m) (K : ℝ) (M : Fin (m+1) → ℝ) : ℝ :=
  curvatureBudget n K (max (M 0) 0) (max (M ⟨1,by omega⟩) 0) (max (M ⟨2,by omega⟩) 0)

lemma backgroundCurvatureBudget_nonneg (n : ℕ) {m : ℕ} (hm : 2 ≤ m) (K : ℝ) (hK : 0 ≤ K) (M : Fin (m+1) → ℝ) :
    0 ≤ backgroundCurvatureBudget n hm K M :=
  curvatureBudget_nonneg n K _ _ _ hK (le_max_right _ _) (le_max_right _ _) (le_max_right _ _)

/-- The actual frame curvature is uniformly bounded over every background with the same
    metric budgets. No compactness bound depending on an individual metric is used. -/
theorem Background.frameCurvatureCoefficient_uniform_bound {Ω : Set (X n)} (hΩ : IsOpen Ω)
    {K : ℝ} (hK : 0 < K) {m : ℕ} (hm : 2 ≤ m) {M : Fin (m+1) → ℝ}
    {g g₁ g₂ : (MetricField n)} {e : (Frame n)} (h : Background Ω K M g g₁ g₂ e)
    {y : (X n)} (hy : y ∈ Ω) (i j a b : (I n)) :
    |frameCurvatureCoefficient g e y (e y i) (e y j) a b| ≤ backgroundCurvatureBudget n hm K M := by
  let M₀ := max (M 0) 0
  let M₁ := max (M ⟨1,by omega⟩) 0
  let M₂ := max (M ⟨2,by omega⟩) 0
  have hM₀ : 0 ≤ M₀ := le_max_right _ _
  have hM₁ : 0 ≤ M₁ := le_max_right _ _
  have hM₂ : 0 ≤ M₂ := le_max_right _ _
  have hg (i j : (I n)) : |g y i j| ≤ M₀ := (h.reference_entry_bound hy i j).trans (le_max_left _ _)
  have hD (i j : (I n)) : ‖fderiv ℝ (fun x => g x i j) y‖ ≤ M₁ :=
    (h.reference_fderiv_bound (by omega) hy i j).trans (le_max_left _ _)
  have hD₂ (i j : (I n)) : ‖fderiv ℝ (fderiv ℝ (fun x => g x i j)) y‖ ≤ M₂ :=
    (h.reference_second_fderiv_bound hm hy i j).trans (le_max_left _ _)
  have hops := h.1.connection_operator_bounds hΩ hK hy M₁ M₂ hM₁ hM₂ hD hD₂
  exact h.1.frameCurvatureCoefficient_bound hK e h.2.2.2.2.2.2.2 hy M₀ _ _ hM₀
    (by positivity) (by positivity) hg hops.1 hops.2 i j a b

end CalderonN
