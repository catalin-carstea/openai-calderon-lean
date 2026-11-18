import Proof.FramePrincipalBounds
noncomputable section
set_option autoImplicit false
open Set
open scoped ContDiff
namespace ShrinkingSpheres

/-- Qualitative smoothness of the SAME physical principal matrix in the chosen frame. -/
lemma Admissible.contDiffOn_framePrincipalCoefficient {Y Ω : Set X} {m : ℕ}
    {K ρ c₀ floor ε : ℝ} {M : Fin (m+1) → ℝ} {Cj : Fin 9 → ℝ} {d : Data}
    (hd : Admissible Y Ω K ρ c₀ M Cj floor ε d) (hSub : Y ⊆ Ω) (hK : 0 < K) (i j : I) :
    ContDiffOn ℝ ∞ (fun x => frameTensorMatrix d.γ d.frame x (principal d.γ d.g₂ x) i j) Y := by
  have h : Elliptic Y K d.γ :=
    ⟨fun a b => (hd.1.1.1 a b).mono hSub,fun x hx => hd.1.1.2 x (hSub hx)⟩
  have h₂ : Elliptic Y K d.g₂ :=
    ⟨fun a b => (hd.1.2.2.1.1 a b).mono hSub,fun x hx => hd.1.2.2.1.2 x (hSub hx)⟩
  exact contDiffOn_frameTensorMatrix d.γ d.frame h
    (fun k => (hd.1.2.2.2.2.2.2.1 k).mono hSub) (principal d.γ d.g₂)
    (fun a b => contDiffOn_principal_entry h h₂ hK a b) i j
end ShrinkingSpheres
