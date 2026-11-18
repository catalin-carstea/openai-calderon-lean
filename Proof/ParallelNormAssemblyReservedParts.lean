import Proof.ParallelNormAssemblyReservedConditional
import Proof.ParallelNormAssemblyReservedSectors

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

/-- An exact corrected model sector estimate, including qualitative
integrability, with constants before all profiles and packets before tests. -/
def UniformCorrectedModelSectorEstimate (Y Ω : Set X) {m : ℕ}
    (K ρ c₀ : ℝ) (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ) (CF CT : ℝ) (k : Fin 3) : Prop :=
  ∀ CB CS CG CK : ℝ,0 ≤ CB → 0 ≤ CS → 0 ≤ CG → 0 ≤ CK →
    ∃ B η C : ℝ,0 < η ∧ η ≤ 1 ∧ 0 ≤ C ∧
    ∀ floor,B ≤ floor → ∀ ε,0 ≤ ε → ε ≤ η → ∀ d,
    Admissible Y Ω K ρ c₀ M Cj floor ε d → ∀ P : PhysicalPrincipalData Y d CF CT,
    ∀ WF : PhysicalFirstCommutatorPacket P CB CS ε,
    ∀ W : ∀ y ∈ Y,PhysicalPotentialQuarticData P y CG CK,
    ∀ φ,Test Y d.γ d.frame φ →
    ∀ (E : HarmonicTestExpansion Y d.γ d.frame φ) (D : AngularModelData E d.radius),
      IntegrableOn (correctedModelSectorComplexDensity P WF W E D k) Y ∧
      |∫ y in Y,correctedModelSectorComplexDensity P WF W E D k y| ≤
        C*ε*energySq Y d.γ d.frame d.radius φ

/-- The complete potential-containing group stays signed until integration. -/
def UniformCorrectedPotentialEstimate (Y Ω : Set X) {m : ℕ}
    (K ρ c₀ : ℝ) (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ) (CF CT : ℝ) : Prop :=
  ∀ CB CS CG CK : ℝ,0 ≤ CB → 0 ≤ CS → 0 ≤ CG → 0 ≤ CK →
    ∃ B η C : ℝ,0 < η ∧ η ≤ 1 ∧ 0 ≤ C ∧
    ∀ floor,B ≤ floor → ∀ ε,0 ≤ ε → ε ≤ η → ∀ d,
    Admissible Y Ω K ρ c₀ M Cj floor ε d → ∀ P : PhysicalPrincipalData Y d CF CT,
    ∀ WF : PhysicalFirstCommutatorPacket P CB CS ε,
    ∀ W : ∀ y ∈ Y,PhysicalPotentialQuarticData P y CG CK,
    ∀ φ,Test Y d.γ d.frame φ →
    ∀ (E : HarmonicTestExpansion Y d.γ d.frame φ) (D : AngularModelData E d.radius),
      IntegrableOn (correctedPotentialMixedComplexDensity P WF W E D) Y ∧
      |∫ y in Y,correctedPotentialMixedComplexDensity P WF W E D y| ≤
        C*ε*energySq Y d.γ d.frame d.radius φ

/-- The corrected model/scalar estimate is a separate producer. The two
remaining producers are the exact model/first sector and all potential terms. -/
theorem uniform_corrected_reserved_estimate_of_model_first_potential
    {Y Ω : Set X} {m : ℕ} (K ρ c₀ : ℝ) (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ)
    (CF CT : ℝ)
    (hScalar : UniformCorrectedModelSectorEstimate Y Ω K ρ c₀ M Cj CF CT 0)
    (hFirst : UniformCorrectedModelSectorEstimate Y Ω K ρ c₀ M Cj CF CT 1)
    (hPotential : UniformCorrectedPotentialEstimate Y Ω K ρ c₀ M Cj CF CT) :
    UniformCorrectedReservedEstimate Y Ω K ρ c₀ M Cj CF CT := by
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
  have hEq : correctedReservedComplexDensity P WF W E D =
      (correctedModelSectorComplexDensity P WF W E D 0+
        correctedModelSectorComplexDensity P WF W E D 1)+
        correctedPotentialMixedComplexDensity P WF W E D := by
    funext y
    simp only [Pi.add_apply]
    rw [corrected_reserved_density_split]
    simp only [remainingCorrectedReservedDensity,correctedModelScalarComplexDensity,
      correctedModelFirstComplexDensity]
    ring
  rw [hEq]
  simp only [Pi.add_apply]
  have hAdd := integral_add (hIS.add hIF) hIP
  simp only [Pi.add_apply] at hAdd
  rw [hAdd,integral_add hIS hIF]
  let iS := ∫ y in Y,correctedModelSectorComplexDensity P WF W E D 0 y
  let iF := ∫ y in Y,correctedModelSectorComplexDensity P WF W E D 1 y
  let iP := ∫ y in Y,correctedPotentialMixedComplexDensity P WF W E D y
  change |iS+iF+iP| ≤ (CS0+CF0+CP0)*ε*energySq Y d.γ d.frame d.radius φ
  calc
    _ ≤ |iS+iF|+|iP| := abs_add_le _ _
    _ ≤ (|iS|+|iF|)+|iP| := add_le_add (abs_add_le iS iF) (le_refl |iP|)
    _ ≤ CS0*ε*energySq Y d.γ d.frame d.radius φ+
        CF0*ε*energySq Y d.γ d.frame d.radius φ+
        CP0*ε*energySq Y d.γ d.frame d.radius φ := add_le_add (add_le_add hBS hBF) hBP
    _ = _ := by ring

end ShrinkingSpheres.ParallelEnergy
