import Proof.PhysicalPotentialGeneratorAdjoints
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option maxSynthPendingDepth 30
set_option maxRecDepth 2400
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set
open scoped ContDiff
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.SphereHarmonic

/-- The flat adjoints can be selected once, independent of the base point.
The empty-domain case needs no physical coefficient graph. -/
theorem uniform_flat_raising_constant_adjoint_higher {Y Ω : Set X}
    (hY : IsOpen Y) (hΩ : IsOpen Ω) (hSub : Y ⊆ Ω) {m : ℕ} (hm : 10 ≤ m)
    (K ρ c₀ : ℝ) (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ)
    (hK : 1 ≤ K) (hρ : 0 < ρ) :
    ∃ η CR : ℝ,0 < η ∧ η ≤ 1 ∧ 0 ≤ CR ∧
      ∀ floor,1 ≤ floor → ∀ ε,0 ≤ ε → ε ≤ η → ∀ d,
      Admissible Y Ω K ρ c₀ M Cj floor ε d →
      ∀ CF CT : ℝ,∀ P : PhysicalPrincipalData Y d CF CT,
      ∃ A : I → SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ),
      ∀ y ∈ Y,∀ i : I,
        (sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)).comp (A i)=
          (flatHalfRaisingL i).adjoint.comp (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)) ∧
        ‖A i‖ ≤ CR := by
  classical
  obtain ⟨η,CR,hη,hη1,hCR,hData⟩ := uniform_physical_potential_generator_adjoints
    hY hΩ hSub hm K ρ c₀ M Cj hK hρ
  refine ⟨η,CR,hη,hη1,hCR,?_⟩
  intro floor hf ε hε hSmall d hd CF CT P
  by_cases hN : Y.Nonempty
  · obtain ⟨y,hy⟩ := hN
    obtain ⟨W⟩ := hData floor hf ε hε hSmall d hd CF CT P y hy
    refine ⟨fun i => W.high (.inr (.inl i)),?_⟩
    intro x hx i
    exact ⟨W.compatible (.inr (.inl i)),by simpa only [potentialGeneratorWeight,mul_one] using W.bound (.inr (.inl i))⟩
  · refine ⟨fun _ => 0,?_⟩
    intro x hx
    exact (hN ⟨x,hx⟩).elim
end ShrinkingSpheres
