import Proof.ParallelNormAssemblyReservedParts

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2800000
set_option maxRecDepth 10000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter MeasureTheory
open scoped ContDiff Topology InnerProductSpace
namespace ShrinkingSpheres.ParallelEnergy

/-- An exact raw cross sector with integrability and frozen-energy bound.
Sector5 is the complete effective-first/potential assignment. -/
def UniformPotentialSectorEstimate (Y Ω : Set X) {m : ℕ}
    (K ρ c₀ : ℝ) (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ) (CF CT : ℝ) (k : Fin 9) : Prop :=
  ∀ CB CS CG CK : ℝ,0 ≤ CB → 0 ≤ CS → 0 ≤ CG → 0 ≤ CK →
    ∃ B η C : ℝ,0 < η ∧ η ≤ 1 ∧ 0 ≤ C ∧
    ∀ floor,B ≤ floor → ∀ ε,0 ≤ ε → ε ≤ η → ∀ d,
    Admissible Y Ω K ρ c₀ M Cj floor ε d → ∀ P : PhysicalPrincipalData Y d CF CT,
    ∀ WF : PhysicalFirstCommutatorPacket P CB CS ε,
    ∀ W : ∀ y ∈ Y,PhysicalPotentialQuarticData P y CG CK,
    ∀ φ,Test Y d.γ d.frame φ →
    ∀ (E : HarmonicTestExpansion Y d.γ d.frame φ) (D : AngularModelData E d.radius),
      IntegrableOn (sectorComplexDensity P WF W E D k) Y ∧
      |∫ y in Y,sectorComplexDensity P WF W E D k y| ≤
        C*ε*energySq Y d.γ d.frame d.radius φ

/-- The scalar/potential, complete-first/potential and corrected
model/potential estimates have separate internal cancellations. -/
theorem uniform_corrected_potential_estimate_of_three_sectors
    {Y Ω : Set X} {m : ℕ} (K ρ c₀ : ℝ) (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ)
    (CF CT : ℝ)
    (hScalar : UniformPotentialSectorEstimate Y Ω K ρ c₀ M Cj CF CT 4)
    (hFirst : UniformPotentialSectorEstimate Y Ω K ρ c₀ M Cj CF CT 5)
    (hPotential : UniformCorrectedModelSectorEstimate Y Ω K ρ c₀ M Cj CF CT 2) :
    UniformCorrectedPotentialEstimate Y Ω K ρ c₀ M Cj CF CT := by
  intro CB CS CG CK hCB hCS hCG hCK
  obtain ⟨BS,ηS,CS0,hηS,hηS1,hCS0,hS⟩ := hScalar CB CS CG CK hCB hCS hCG hCK
  obtain ⟨BF,ηF,CF0,hηF,hηF1,hCF0,hF⟩ := hFirst CB CS CG CK hCB hCS hCG hCK
  obtain ⟨BP,ηP,CP0,hηP,hηP1,hCP0,hP⟩ := hPotential CB CS CG CK hCB hCS hCG hCK
  refine ⟨max BS (max BF BP),min ηS (min ηF ηP),CS0+CF0+CP0,
    lt_min hηS (lt_min hηF hηP),(min_le_left _ _).trans hηS1,by positivity,?_⟩
  intro floor hf ε hε hSmall d hd P WF W φ hφ E D
  have hfS := (le_max_left BS (max BF BP)).trans hf
  have hfF := (le_max_left BF BP).trans ((le_max_right BS (max BF BP)).trans hf)
  have hfP := (le_max_right BF BP).trans ((le_max_right BS (max BF BP)).trans hf)
  have heS := hSmall.trans (min_le_left ηS (min ηF ηP))
  have heF := (hSmall.trans (min_le_right ηS (min ηF ηP))).trans (min_le_left ηF ηP)
  have heP := (hSmall.trans (min_le_right ηS (min ηF ηP))).trans (min_le_right ηF ηP)
  obtain ⟨hIS,hBS⟩ := hS floor hfS ε hε heS d hd P WF W φ hφ E D
  obtain ⟨hIF,hBF⟩ := hF floor hfF ε hε heF d hd P WF W φ hφ E D
  obtain ⟨hIP,hBP⟩ := hP floor hfP ε hε heP d hd P WF W φ hφ E D
  have hEq : correctedPotentialMixedComplexDensity P WF W E D=
      (sectorComplexDensity P WF W E D 4+sectorComplexDensity P WF W E D 5)+
        correctedModelSectorComplexDensity P WF W E D 2 := rfl
  refine ⟨by rw [hEq];exact (hIS.add hIF).add hIP,?_⟩
  rw [hEq]
  simp only [Pi.add_apply]
  have hAdd := integral_add (hIS.add hIF) hIP
  simp only [Pi.add_apply] at hAdd
  rw [hAdd,integral_add hIS hIF]
  let iS := ∫ y in Y,sectorComplexDensity P WF W E D 4 y
  let iF := ∫ y in Y,sectorComplexDensity P WF W E D 5 y
  let iP := ∫ y in Y,correctedModelSectorComplexDensity P WF W E D 2 y
  change |iS+iF+iP| ≤ (CS0+CF0+CP0)*ε*energySq Y d.γ d.frame d.radius φ
  calc
    _ ≤ |iS+iF|+|iP| := abs_add_le _ _
    _ ≤ (|iS|+|iF|)+|iP| := add_le_add (abs_add_le iS iF) (le_refl |iP|)
    _ ≤ CS0*ε*energySq Y d.γ d.frame d.radius φ+
        CF0*ε*energySq Y d.γ d.frame d.radius φ+
        CP0*ε*energySq Y d.γ d.frame d.radius φ := add_le_add (add_le_add hBS hBF) hBP
    _ = _ := by ring

end ShrinkingSpheres.ParallelEnergy
