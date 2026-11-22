module

public import Proof.Manuscript.Corollary13

public section

open Set
open scoped ContDiff Manifold

namespace CalderonPaper

theorem scalarConductivitiesAgreeAtBoundary {n : ℕ} [NeZero n] (hn : 3 ≤ n)
    {Ω : Set (EuclideanSpace ℝ (Fin n))} (hΩ : IsOpen Ω)
    (hbounded : Bornology.IsBounded Ω) (hconn : IsConnected Ω)
    [ChartedSpace (EuclideanHalfSpace n) ↥(closure Ω)]
    [IsManifold (𝓡∂ n) ∞ ↥(closure Ω)] (D : EuclideanClosure Ω)
    {Γ : Set ↥(frontier Ω)} (hΓ : IsOpen Γ) (hΓne : Γ.Nonempty)
    {γ₁ γ₂ : EuclideanSpace ℝ (Fin n) → ℝ}
    (hγ₁ : SmoothThrough (closure Ω) γ₁) (hγ₂ : SmoothThrough (closure Ω) γ₂)
    (hpos₁ : ∀ x ∈ closure Ω, 0 < γ₁ x) (hpos₂ : ∀ x ∈ closure Ω, 0 < γ₂ x)
    (hDN : ScalarPatchEnergyEqual D hΩ γ₁ γ₂ Γ)
    (p : ↥(frontier Ω)) : γ₁ p = γ₂ p :=
  corollary13 hn hΩ hbounded hconn D hΓ hΓne hγ₁ hγ₂ hpos₁ hpos₂ hDN p.property.1

end CalderonPaper
