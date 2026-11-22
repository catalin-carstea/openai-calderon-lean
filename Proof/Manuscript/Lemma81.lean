module

public import Proof.Manuscript.Lemma81Defs
import Proof.Manuscript.ConformalBoundary
import Proof.Manuscript.ConformalPropagation

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
    EqOn F id (closure Ω) ∧ EqOn b (fun _ => 0) (closure Ω) := by
  obtain ⟨p, hpΓ⟩ := hΓne
  have hpΩ : (p : EuclideanSpace ℝ (Fin n)) ∈ closure Ω := p.property.1
  obtain ⟨U, hU, hpU, G, hG, hEqG⟩ := hF.2.2.1 p hpΩ
  obtain ⟨V, hV, hpV, B, hB, hEqB⟩ := hb p hpΩ
  have hG' := hG.mono (inter_subset_left : U ∩ V ⊆ U)
  have hB' := hB.mono (inter_subset_right : U ∩ V ⊆ V)
  have hEqG' : EqOn G F ((U ∩ V) ∩ closure Ω) :=
    fun _ hy => hEqG ⟨hy.1.1, hy.2⟩
  have hEqB' : EqOn B b ((U ∩ V) ∩ closure Ω) :=
    fun _ hy => hEqB ⟨hy.1.2, hy.2⟩
  have hpUV : (p : EuclideanSpace ℝ (Fin n)) ∈ U ∩ V := ⟨hpU, hpV⟩
  obtain ⟨hpDG, hpB⟩ := conformal_boundary_first_jet hn hΩ hboundary hF.2.1 hΓ hfix
    hconformal (hU.inter hV) p hpΓ hpUV hG' hB' hEqG' hEqB'
  have hpDB := conformal_boundary_exponent_derivative hn hΩ hboundary hF.2.1 hΓ hfix
    hconformal (hU.inter hV) p hpΓ hpUV hG' hB' hEqG' hEqB'
  exact propagate_conformal_anchor hn hΩ hconn.isPreconnected (hU.inter hV)
    hF.2.2.1 hb hconformal hG' hB' hEqG' hEqB' hpUV hpΩ (hfix p hpΓ) hpB hpDG hpDB

end CalderonPaper
