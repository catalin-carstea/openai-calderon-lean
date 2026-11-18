import Proof.ParallelNormAssemblyReservedPotentialParts
import Proof.ScalarCovariantAdjointDefect

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
open OAI.AnisotropicCalderon.SphereHarmonic

variable {Y : Set X} {d : Data} {CF CT CB CS CG CK ε : ℝ}

/-- Literal scalar-transpose defect against the SAME actual potential
adjoint, including the original cross-sector factor two. -/
def scalarPotentialDefectCoreDensity (P : PhysicalPrincipalData Y d CF CT)
    (W : ∀ y ∈ Y,PhysicalPotentialQuarticData P y CG CK)
    (U : X → SphereSobolev (5/2:ℝ)) (y : X) : ℝ :=
  2*metricDensity d.γ y*⟪scalarCovariantAdjointDefectSection d (metricDensity d.γ)
    (scalarPrincipalMatrix d.γ d.g₂ d.radius) (fiveHalfToTwoSection U) y,
    P.potentialQuadraticAdjointCoreSection W U y⟫_ℝ

/-- Both original real and imaginary test components. -/
def scalarPotentialDefectComplexDensity (P : PhysicalPrincipalData Y d CF CT)
    (W : ∀ y ∈ Y,PhysicalPotentialQuarticData P y CG CK)
    {φ : Field} (E : HarmonicTestExpansion Y d.γ d.frame φ) (y : X) : ℝ :=
  scalarPotentialDefectCoreDensity P W (E.realHigherSobolevSection (5/2:ℝ) (by norm_num)) y+
    scalarPotentialDefectCoreDensity P W (E.imagHigherSobolevSection (5/2:ℝ) (by norm_num)) y

/-- The defect-corrected literal raw sector. Its exact identification with
the symmetric scalar/skew-quadratic Green density is retained by the
norm-assembly author. -/
def scalarPotentialLeadingComplexDensity (P : PhysicalPrincipalData Y d CF CT)
    (WF : PhysicalFirstCommutatorPacket P CB CS ε)
    (W : ∀ y ∈ Y,PhysicalPotentialQuarticData P y CG CK)
    {φ : Field} (E : HarmonicTestExpansion Y d.γ d.frame φ)
    (D : AngularModelData E d.radius) (y : X) : ℝ :=
  sectorComplexDensity P WF W E D 4 y+scalarPotentialDefectComplexDensity P W E y

/-- The independent bounded defect task. Constants precede profiles;
the SAME arbitrary physical packets precede the test and expansions. -/
def UniformScalarPotentialDefectEstimate (Y Ω : Set X) {m : ℕ}
    (K ρ c₀ : ℝ) (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ) (CF CT : ℝ) : Prop :=
  ∀ CB CS CG CK : ℝ,0 ≤ CB → 0 ≤ CS → 0 ≤ CG → 0 ≤ CK →
    ∃ B η C : ℝ,0 < η ∧ η ≤ 1 ∧ 0 ≤ C ∧
    ∀ floor,B ≤ floor → ∀ ε,0 ≤ ε → ε ≤ η → ∀ d,
    Admissible Y Ω K ρ c₀ M Cj floor ε d → ∀ P : PhysicalPrincipalData Y d CF CT,
    ∀ WF : PhysicalFirstCommutatorPacket P CB CS ε,
    ∀ W : ∀ y ∈ Y,PhysicalPotentialQuarticData P y CG CK,
    ∀ φ,Test Y d.γ d.frame φ →
    ∀ (E : HarmonicTestExpansion Y d.γ d.frame φ) (D : AngularModelData E d.radius),
      IntegrableOn (scalarPotentialDefectComplexDensity P W E) Y ∧
      |∫ y in Y,scalarPotentialDefectComplexDensity P W E y| ≤
        C*ε^2*energySq Y d.γ d.frame d.radius φ

def UniformScalarPotentialLeadingEstimate (Y Ω : Set X) {m : ℕ}
    (K ρ c₀ : ℝ) (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ) (CF CT : ℝ) : Prop :=
  ∀ CB CS CG CK : ℝ,0 ≤ CB → 0 ≤ CS → 0 ≤ CG → 0 ≤ CK →
    ∃ B η C : ℝ,0 < η ∧ η ≤ 1 ∧ 0 ≤ C ∧
    ∀ floor,B ≤ floor → ∀ ε,0 ≤ ε → ε ≤ η → ∀ d,
    Admissible Y Ω K ρ c₀ M Cj floor ε d → ∀ P : PhysicalPrincipalData Y d CF CT,
    ∀ WF : PhysicalFirstCommutatorPacket P CB CS ε,
    ∀ W : ∀ y ∈ Y,PhysicalPotentialQuarticData P y CG CK,
    ∀ φ,Test Y d.γ d.frame φ →
    ∀ (E : HarmonicTestExpansion Y d.γ d.frame φ) (D : AngularModelData E d.radius),
      IntegrableOn (scalarPotentialLeadingComplexDensity P WF W E D) Y ∧
      |∫ y in Y,scalarPotentialLeadingComplexDensity P WF W E D y| ≤
        C*ε^2*energySq Y d.γ d.frame d.radius φ

/-- Exact checked consumer of the independent defect task and the
retained symmetric Green task. No mathematical sector estimate is hidden. -/
theorem uniform_scalar_potential_sector_of_leading_defect
    {Y Ω : Set X} {m : ℕ} (K ρ c₀ : ℝ) (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ)
    (CF CT : ℝ)
    (hL : UniformScalarPotentialLeadingEstimate Y Ω K ρ c₀ M Cj CF CT)
    (hF : UniformScalarPotentialDefectEstimate Y Ω K ρ c₀ M Cj CF CT) :
    UniformPotentialSectorEstimate Y Ω K ρ c₀ M Cj CF CT 4 := by
  intro CB CS CG CK hCB hCS hCG hCK
  obtain ⟨BL,ηL,CL,hηL,hηL1,hCL,hLeading⟩ := hL CB CS CG CK hCB hCS hCG hCK
  obtain ⟨BF,ηF,CF0,hηF,hηF1,hCF0,hDefect⟩ := hF CB CS CG CK hCB hCS hCG hCK
  refine ⟨max BL BF,min ηL ηF,CL+CF0,lt_min hηL hηF,
    (min_le_left _ _).trans hηL1,add_nonneg hCL hCF0,?_⟩
  intro floor hf ε hε hSmall d hd P WF W φ hφ E D
  obtain ⟨hIL,hBL⟩ := hLeading floor ((le_max_left _ _).trans hf) ε hε
    (hSmall.trans (min_le_left _ _)) d hd P WF W φ hφ E D
  obtain ⟨hIF,hBF⟩ := hDefect floor ((le_max_right _ _).trans hf) ε hε
    (hSmall.trans (min_le_right _ _)) d hd P WF W φ hφ E D
  have hEq : sectorComplexDensity P WF W E D 4=
      scalarPotentialLeadingComplexDensity P WF W E D-scalarPotentialDefectComplexDensity P W E := by
    funext y
    simp only [Pi.sub_apply,scalarPotentialLeadingComplexDensity,add_sub_cancel_right]
  refine ⟨by rw [hEq];exact hIL.sub hIF,?_⟩
  rw [hEq]
  have hInt := integral_sub hIL hIF
  change |∫ y in Y,scalarPotentialLeadingComplexDensity P WF W E D y-scalarPotentialDefectComplexDensity P W E y| ≤ _
  rw [hInt]
  have hε1 : ε ≤ 1 := (hSmall.trans (min_le_left _ _)).trans hηL1
  have hεsq : ε^2 ≤ ε := by nlinarith
  have hEn := energySq_nonneg Y d.γ d.frame d.radius φ
  calc
    _ ≤ |∫ y in Y,scalarPotentialLeadingComplexDensity P WF W E D y|+
        |∫ y in Y,scalarPotentialDefectComplexDensity P W E y| := abs_sub _ _
    _ ≤ CL*ε^2*energySq Y d.γ d.frame d.radius φ+
        CF0*ε^2*energySq Y d.γ d.frame d.radius φ := add_le_add hBL hBF
    _ = (CL+CF0)*ε^2*energySq Y d.γ d.frame d.radius φ := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hεsq (add_nonneg hCL hCF0)) hEn

end ShrinkingSpheres.ParallelEnergy
