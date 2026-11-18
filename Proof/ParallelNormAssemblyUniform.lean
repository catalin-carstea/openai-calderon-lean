import Proof.ParallelNormAssemblyGrouped
import Proof.ConstantBoundaryCoefficients

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2800000
set_option maxRecDepth 10000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter MeasureTheory
open scoped ContDiff Topology InnerProductSpace ENNReal
namespace ShrinkingSpheres.ParallelEnergy
open OAI.AnisotropicCalderon.SphereHarmonic OAI.AnisotropicCalderon.DirichletFamily

/-- The checked scalar and potential comparisons and common-core packet
producer discharge all already completed sectors. Only the exact worker
first-self and scalar/first estimates and the integrator's complete reserved
sum remain in hRemaining. Its universality over the selected WF/W is the
explicit compatibility needed to use the same packets before every test. -/
theorem uniform_physical_truncated_norm_comparison_of_uniform_remaining_sectors
    {Y Ω : Set X} (hY : IsOpen Y) (hΩ : IsOpen Ω) (hSub : Y ⊆ Ω)
    {m : ℕ} (hm : 10 ≤ m) (K ρ c₀ : ℝ) (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ)
    (hK : 1 ≤ K) (hρ : 0 < ρ) (CF CT : ℝ)
    (hRemaining : ∀ CB CS CG CK : ℝ,0 ≤ CB → 0 ≤ CS → 0 ≤ CG → 0 ≤ CK →
      ∃ B η : ℝ,∃ C : Fin 5 → ℝ,0 < η ∧ η ≤ 1 ∧ (∀ i,0 ≤ C i) ∧
      ∀ floor,B ≤ floor → ∀ ε,0 ≤ ε → ε ≤ η → ∀ d,
      Admissible Y Ω K ρ c₀ M Cj floor ε d → ∀ P : PhysicalPrincipalData Y d CF CT,
      ∀ WF : PhysicalFirstCommutatorPacket P CB CS ε,
      ∀ W : ∀ y ∈ Y,PhysicalPotentialQuarticData P y CG CK,
      RemainingGroupedSectorBounds P WF W C) :
    UniformPhysicalTruncatedNormComparison Y Ω K ρ c₀ M Cj CF CT := by
  obtain ⟨ηP,CB,CS,CG,CK,CP,hηP,hηP1,hCB,hCS,hCG,hCK,hCP,hPackets⟩ :=
    uniform_physical_truncated_core_calculus hY hΩ hSub hm K ρ c₀ M Cj hK hρ CF
  obtain ⟨B,ηR,C,hηR,hηR1,hC,hRest⟩ := hRemaining CB CS CG CK hCB hCS hCG hCK
  obtain ⟨Q,hQ⟩ := exists_unit_boundary_coefficient
  let c : Fin 5 → ℝ := fun i => if i=2 then CP else C i
  have hc (i) : 0 ≤ c i := by
    dsimp only [c]
    split_ifs
    · exact hCP
    · exact hC i
  apply uniform_physical_truncated_norm_comparison_of_grouped_sectors hY hΩ hSub (by omega)
    hK Q (max 1 B) (min ηP ηR) CB CS CG CK c hQ (lt_min hηP hηR)
    ((min_le_left _ _).trans hηP1) hc hCG hCK
  intro floor hf ε hε hSmall d hd P
  have hf1 := (le_max_left 1 B).trans hf
  have hfB := (le_max_right 1 B).trans hf
  obtain ⟨WF,W,hCalc,hPot⟩ := hPackets floor hf1 ε hε
    (hSmall.trans (min_le_left _ _)) d hd CT P
  refine ⟨WF,W,hCalc,?_,?_⟩
  · simpa [c] using hPot
  · have hh := hRest floor hfB ε hε (hSmall.trans (min_le_right _ _)) d hd P WF W
    simpa [RemainingGroupedSectorBounds,c] using hh

end ShrinkingSpheres.ParallelEnergy
