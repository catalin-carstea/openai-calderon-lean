import Proof.PhysicalPotentialActualNorm
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2600000
set_option maxSynthPendingDepth 30
set_option maxRecDepth 2600
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set
open scoped ContDiff Topology
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.SphereHarmonic

lemma Admissible.contDiffOn_potentialWordCoefficient {Y Ω : Set X}
    (hY : IsOpen Y) (hSub : Y ⊆ Ω) {m : ℕ} {K ρ c₀ floor ε : ℝ}
    {M : Fin (m+1) → ℝ} {Cj : Fin 9 → ℝ} {d : Data}
    (hd : Admissible Y Ω K ρ c₀ M Cj floor ε d) (hK : 0 < K)
    (a b : PhysicalPotentialGeneratorIndex) :
    ContDiffOn ℝ ∞ (fun y => PhysicalPrincipalData.potentialWordCoefficient d y a b) Y := by
  have h : Elliptic Y K d.γ := ⟨fun i j => (hd.1.1.1 i j).mono hSub,fun x hx => hd.1.1.2 x (hSub hx)⟩
  have h₂ : Elliptic Y K d.g₂ := ⟨fun i j => (hd.1.2.2.1.1 i j).mono hSub,fun x hx => hd.1.2.2.1.2 x (hSub hx)⟩
  have he (i : I) := (hd.1.2.2.2.2.2.2.1 i).mono hSub
  have hQ (i j : I) := hd.contDiffOn_framePrincipalCoefficient hSub hK i j
  have hr := hd.2.2.2.2.1.1
  have hr0 := fun y hy => (hd.2.2.2.2.1.2 y hy).1.ne'
  have hLog := hr.log hr0
  have hf (i : I) := (hLog.fderiv_of_isOpen (m:=∞) hY (by simp)).clm_apply (he i)
  have ht (i : I) := hr.mul (hf i)
  have hEntries (i j : I) : ContDiffOn ℝ ∞ (fun y => (principal d.γ d.g₂ y-(d.γ y)⁻¹) i j) Y := by
    simpa only [Matrix.sub_apply] using (contDiffOn_principal_entry h h₂ hK i j).sub (h.contDiffOn_inverse_entry hK i j)
  have hDiff (i j : I) := (contDiffOn_frameTensorMatrix d.γ d.frame h he
    (fun y => principal d.γ d.g₂ y-(d.γ y)⁻¹) hEntries i j).div hr hr0
  rcases a with u | (i | i) <;> rcases b with v | (j | j)
  · exact ContDiffOn.sum (fun i _ => ContDiffOn.sum (fun j _ => (hQ i j).mul ((hr.mul (hf i)).mul (hf j))))
  · exact contDiffOn_const
  · exact ContDiffOn.sum (fun i _ => (hQ i j).mul (ht i))
  · exact contDiffOn_const.mul (ContDiffOn.sum (fun j _ => ((hQ i j).sub contDiffOn_const).mul (hf j)))
  · exact hDiff i j
  · exact hQ i j
  · exact ContDiffOn.sum (fun j _ => (hQ i j).mul (ht j))
  · exact hQ i j
  · exact hr.mul (hQ i j)

lemma PhysicalPrincipalData.potentialQuadraticHalfL_smooth {Y Ω : Set X}
    (hY : IsOpen Y) (hSub : Y ⊆ Ω) {m : ℕ} {K ρ c₀ floor ε CF CT : ℝ}
    {M : Fin (m+1) → ℝ} {Cj : Fin 9 → ℝ} {d : Data}
    (P : PhysicalPrincipalData Y d CF CT) (hd : Admissible Y Ω K ρ c₀ M Cj floor ε d) (hK : 0 < K) :
    ContDiffOn ℝ ∞ P.potentialQuadraticHalfL Y := by
  have hWords : ContDiffOn ℝ ∞ P.potentialWordMatrixL Y :=
    ContDiffOn.sum (fun a _ => ContDiffOn.sum (fun b _ =>
      (hd.contDiffOn_potentialWordCoefficient hY hSub hK a b).smul
        (((P.potential_generator_smooth a).1).clm_comp ((P.potential_generator_smooth b).2))))
  exact hWords.congr (fun y _ => P.potentialQuadraticHalfL_eq_word_matrix y)
end ShrinkingSpheres
