module

public import Proof.Manuscript.MovingTraceSymbols

import Mathlib.Tactic

public section

noncomputable section

open Set Filter
open scoped ContDiff Topology BigOperators

namespace CalderonPaper

variable {P : Type} {dim : ℕ} {Y : Set (CalderonN.X dim)}
  {β : P → CalderonN.X dim → ℝ} {order : ℤ}

/-- Local symbol seminorms agree on an open base domain when the
underlying symbols agree on the domain at every angular point. -/
theorem SymbolSeminormBounds.congrOn {a b : LocalAngularSymbol P dim}
    (ha : SymbolSeminormBounds Y β order a) (hY : IsOpen Y)
    (hEq : ∀ t y, y ∈ Y → ∀ x ξ, a t y x ξ = b t y x ξ) :
    SymbolSeminormBounds Y β order b := by
  intro j k l hj
  obtain ⟨C,hC,h⟩ := ha j k l hj
  refine ⟨C,hC,fun t y hy x ξ => ?_⟩
  have he : (fun p => iteratedFDeriv ℝ k (fun x' => iteratedFDeriv ℝ l (a t p x') ξ) x) =ᶠ[𝓝 y]
      (fun p => iteratedFDeriv ℝ k (fun x' => iteratedFDeriv ℝ l (b t p x') ξ) x) := by
    filter_upwards [hY.mem_nhds hy] with p hp
    have hPoint : a t p = b t p := by
      funext z η
      exact hEq t p hp z η
    rw [hPoint]
  rw [← (he.iteratedFDeriv ℝ j).eq_of_nhds]
  exact h t y hy x ξ

/-- If the leading homogeneous term in a classical expansion vanishes,
the shifted expansion certifies the same symbol at one lower order.
The base weight and all the stated seminorms carry through the shift. -/
theorem UniformClassicalAngularSymbol.lower_order_of_principal_zero
    {a : LocalAngularSymbol P dim} (hY : IsOpen Y)
    (ha : ∀ t, ContDiffOn ℝ ∞ (fun q : CalderonN.X dim ×
      (AngularCoordinates dim × AngularCoordinates dim) => a t q.1 q.2.1 q.2.2) (Y ×ˢ univ))
    {χ : AngularCoordinates dim → ℝ} {h : ℕ → LocalAngularSymbol P dim}
    (hχ : ContDiff ℝ ∞ χ)
    (hχ₀ : ∀ ξ, ‖ξ‖ ≤ 1 → χ ξ = 0) (hχ₁ : ∀ ξ, 2 ≤ ‖ξ‖ → χ ξ = 1)
    (hh : ∀ j t, ContDiffOn ℝ ∞
      (fun q : CalderonN.X dim × (AngularCoordinates dim × AngularCoordinates dim) =>
        h j t q.1 q.2.1 q.2.2) (Y ×ˢ (univ ×ˢ ({0}ᶜ : Set (AngularCoordinates dim)))))
    (hHom : ∀ j t y, y ∈ Y → ∀ x ξ, ξ ≠ 0 → ∀ r : ℝ, 0 < r →
      h j t y x (r • ξ) = ((r ^ ((order : ℝ) - j) : ℝ) : ℂ) * h j t y x ξ)
    (hRem : ∀ N : ℕ, SymbolSeminormBounds Y β (order - (N : ℤ))
      (fun t y x ξ => a t y x ξ - (χ ξ : ℂ) * ∑ j ∈ Finset.range N, h j t y x ξ))
    (hZero : ∀ t y, y ∈ Y → ∀ x ξ, ξ ≠ 0 → h 0 t y x ξ = 0) :
    UniformClassicalAngularSymbol Y β (order - 1) a := by
  let h' (j : ℕ) := h (j+1)
  have hZeroCut (t : P) (y : CalderonN.X dim) (hy : y ∈ Y) (x ξ : AngularCoordinates dim) :
      (χ ξ : ℂ) * h 0 t y x ξ = 0 := by
    by_cases hξ : ξ = 0
    · rw [hχ₀ ξ (by simp [hξ]),Complex.ofReal_zero,zero_mul]
    · rw [hZero t y hy x ξ hξ,mul_zero]
  have hRem' (N : ℕ) : SymbolSeminormBounds Y β (order - 1 - (N : ℤ))
      (fun t y x ξ => a t y x ξ - (χ ξ : ℂ) * ∑ j ∈ Finset.range N, h' j t y x ξ) := by
    have hInt : order - 1 - (N : ℤ) = order - ((N+1 : ℕ) : ℤ) := by push_cast; ring
    rw [hInt]
    refine (hRem (N+1)).congrOn hY ?_
    intro t y hy x ξ
    rw [Finset.sum_range_succ',mul_add,hZeroCut t y hy x ξ]
    simp only [add_zero,h']
  refine ⟨ha,?_,χ,h',hχ,hχ₀,hχ₁,fun j => hh (j+1),?_,hRem'⟩
  · simpa only [Nat.cast_zero,sub_zero,Finset.range_zero,Finset.sum_empty,mul_zero] using hRem' 0
  · intro j t y hy x ξ hξ r hr
    change h (j+1) t y x (r • ξ) =
      ((r ^ (((order-1 : ℤ) : ℝ) - j) : ℝ) : ℂ) * h (j+1) t y x ξ
    rw [hHom (j+1) t y hy x ξ hξ r hr]
    congr 3
    push_cast
    ring

end CalderonPaper
