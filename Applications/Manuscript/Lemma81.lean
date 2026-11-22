module

public import Proof.Manuscript.Lemma81

public section

open Set

namespace CalderonPaper

theorem conformalScaleOneOnDomain {n : ℕ} (hn : 3 ≤ n)
    {Ω : Set (EuclideanSpace ℝ (Fin n))} (hΩ : IsOpen Ω) (hconn : IsConnected Ω)
    (hboundary : HasSmoothEuclideanBoundary Ω)
    {F : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)} {b : EuclideanSpace ℝ (Fin n) → ℝ}
    (hF : IsClosureDiffeomorphism Ω F) (hb : SmoothThrough (closure Ω) b)
    (hconformal : EuclideanConformalOn Ω F b)
    {Γ : Set (frontier Ω)} (hΓ : IsOpen Γ) (hΓne : Γ.Nonempty)
    (hfix : ∀ p : frontier Ω, p ∈ Γ → F p = (p : EuclideanSpace ℝ (Fin n))) :
    ∀ x ∈ Ω, Real.exp (2 * b x) = 1 := by
  intro x hx
  rw [(lemma81 hn hΩ hconn hboundary hF hb hconformal hΓ hΓne hfix).2 (subset_closure hx)]
  simp

end CalderonPaper
