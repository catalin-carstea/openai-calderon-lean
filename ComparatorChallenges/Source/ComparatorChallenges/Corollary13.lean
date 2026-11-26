module

public import Proof.Manuscript.ScalarConductivityDefs

public section

open Set
open scoped ContDiff Manifold

namespace CalderonPaper

/-- Corollary 1.3. Smooth scalar uniqueness from one patch. -/
theorem corollary13 {n : ℕ} [NeZero n] (hn : 3 ≤ n)
    {Ω : Set (EuclideanSpace ℝ (Fin n))} (hΩ : IsOpen Ω)
    (hbounded : Bornology.IsBounded Ω) (hconn : IsConnected Ω)

    -- Smooth model of the Euclidean closure.
    [ChartedSpace (EuclideanHalfSpace n) ↥(closure Ω)]
    [IsManifold (𝓡∂ n) ∞ ↥(closure Ω)] (D : EuclideanClosure Ω)

    -- Patch and strictly positive conductivities.
    {Γ : Set ↥(frontier Ω)} (hΓ : IsOpen Γ) (hΓne : Γ.Nonempty)
    {γ₁ γ₂ : EuclideanSpace ℝ (Fin n) → ℝ}
    (hγ₁ : SmoothThrough (closure Ω) γ₁) (hγ₂ : SmoothThrough (closure Ω) γ₂)
    (hpos₁ : ∀ x ∈ closure Ω, 0 < γ₁ x) (hpos₂ : ∀ x ∈ closure Ω, 0 < γ₂ x)
    (hDN : ScalarPatchEnergyEqual D hΩ γ₁ γ₂ Γ) :
    EqOn γ₁ γ₂ (closure Ω) := by sorry

end CalderonPaper
