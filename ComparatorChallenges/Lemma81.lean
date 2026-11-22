module

public import ComparatorChallenges.Frozen.Manuscript.Lemma81Defs

public section

open Set

namespace CalderonPaper

/-- Lemma 8.1. Conformal rigidity at a boundary patch. -/
theorem lemma81 {n : ℕ} (hn : 3 ≤ n)
    {Ω : Set (EuclideanSpace ℝ (Fin n))} (hΩ : IsOpen Ω) (hconn : IsConnected Ω)
    (hboundary : HasSmoothEuclideanBoundary Ω)
    {F : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)} {b : EuclideanSpace ℝ (Fin n) → ℝ}
    (hF : IsClosureDiffeomorphism Ω F) (hb : SmoothThrough (closure Ω) b)
    (hconformal : EuclideanConformalOn Ω F b)
    {Γ : Set (frontier Ω)} (hΓ : IsOpen Γ) (hΓne : Γ.Nonempty)
    (hfix : ∀ p : frontier Ω, p ∈ Γ → F p = (p : EuclideanSpace ℝ (Fin n))) :
    EqOn F id (closure Ω) ∧ EqOn b (fun _ => 0) (closure Ω) := sorry

end CalderonPaper
