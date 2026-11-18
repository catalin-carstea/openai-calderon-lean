import Proof.ParallelScalarFirstDecomposition
import Proof.ParallelScalarFirstDefectIntegral

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2800000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
open Set Filter MeasureTheory
namespace ShrinkingSpheres.ParallelEnergy

/-- The exact remaining scalar-second / covariant-adjoint-jet producer.
This conditional helper is internal proof organization, not a new
assumption of the selected proposition. -/
def ScalarFirstJetBound (Y Ω : Set X) (K ρ c₀ : ℝ) {m : ℕ}
    (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ) (CF CT CB CS : ℝ) : Prop :=
  ∃ η C : ℝ,0 < η ∧ η ≤ 1 ∧ 0 ≤ C ∧
    ∀ floor,1 ≤ floor → ∀ ε,0 ≤ ε → ε ≤ η → ∀ d,
    Admissible Y Ω K ρ c₀ M Cj floor ε d → ∀ P : PhysicalPrincipalData Y d CF CT,
    ∀ WF : PhysicalFirstCommutatorPacket P CB CS ε,
    ∀ φ : Field,∀ E : HarmonicTestExpansion Y d.γ d.frame φ,∀ D : AngularModelData E d.radius,
    Test Y d.γ d.frame φ → IntegrableOn (scalarFirstJetComplexDensity P WF E) Y ∧
      |∫ y in Y,scalarFirstJetComplexDensity P WF E y| ≤ C*ε^2*energySq Y d.γ d.frame d.radius φ

/-- Checked assembly of the exact assigned paired cross estimate from
the single remaining jet contribution. Leading cancellation, scalar
defect, all 27 coordinate contractions, real/imaginary components and
factor two are already proved in the imported producers. -/
theorem uniform_scalar_first_cross_bound_of_jet_bound {Y Ω : Set X}
    (hY : IsOpen Y) (hΩ : IsOpen Ω) (hSub : Y ⊆ Ω) {m : ℕ} (hm : 10 ≤ m)
    (K ρ c₀ : ℝ) (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ)
    (hK : 1 ≤ K) (hρ : 0 < ρ) (CF CT CB CS CG CK : ℝ) (hCG : 0 ≤ CG) (hCK : 0 ≤ CK)
    (hJet : ScalarFirstJetBound Y Ω K ρ c₀ M Cj CF CT CB CS) :
    ∃ η C : ℝ,0 < η ∧ η ≤ 1 ∧ 0 ≤ C ∧
      ∀ floor,1 ≤ floor → ∀ ε,0 ≤ ε → ε ≤ η → ∀ d,
      Admissible Y Ω K ρ c₀ M Cj floor ε d → ∀ P : PhysicalPrincipalData Y d CF CT,
      ∀ WF : PhysicalFirstCommutatorPacket P CB CS ε,
      ∀ W : ∀ y ∈ Y,PhysicalPotentialQuarticData P y CG CK,
      ∀ φ : Field,∀ E : HarmonicTestExpansion Y d.γ d.frame φ,
      ∀ D : AngularModelData E d.radius,Test Y d.γ d.frame φ →
        IntegrableOn (scalarFirstComplexDensity P WF W E) Y ∧
          |∫ y in Y,scalarFirstComplexDensity P WF W E y| ≤ C*ε*energySq Y d.γ d.frame d.radius φ := by
  obtain ⟨ηL,CL,hηL,hηL1,hCL,hLead⟩ := uniform_scalar_first_leading_cross_bound hY hΩ hSub hm K ρ c₀ M Cj hK hρ
  obtain ⟨ηF,CF0,hηF,hηF1,hCF0,hDefect⟩ := uniform_scalar_first_defect_cross_bound hY hΩ hSub hm K ρ c₀ M Cj hK hρ
  obtain ⟨ηJ,CJ,hηJ,hηJ1,hCJ,hJetData⟩ := hJet
  let C := CL+CJ+CF0
  have hC : 0 ≤ C := by dsimp only [C];positivity
  refine ⟨min ηL (min ηJ ηF),C,lt_min hηL (lt_min hηJ hηF),(min_le_left _ _).trans hηL1,hC,?_⟩
  intro floor hf ε hε hSmall d hd P WF W φ E D hφ
  have hL := hLead floor hf ε hε (hSmall.trans (min_le_left _ _)) d hd CF CT CB CS P WF φ E D hφ
  have hJ := hJetData floor hf ε hε (hSmall.trans ((min_le_right _ _).trans (min_le_left _ _))) d hd P WF φ E D hφ
  have hF := hDefect floor hf ε hε (hSmall.trans ((min_le_right _ _).trans (min_le_right _ _))) d hd CF CT CB CS CG CK hCG hCK P WF W φ E D hφ
  have hEq : scalarFirstComplexDensity P WF W E =ᵐ[volume.restrict Y]
      (fun y => scalarFirstLeadingComplexDensity P E y+scalarFirstJetComplexDensity P WF E y+
        scalarFirstDefectComplexDensity P WF W E y) := by
    filter_upwards [ae_restrict_mem hY.measurableSet] with y hy
    exact scalarFirstComplexDensity_decomposition hY hΩ hSub hd (zero_lt_one.trans_le hK) P WF W E hy
  have hInt := ((hL.1.add hJ.1).add hF.1).congr hEq.symm
  have hIntegral : (∫ y in Y,scalarFirstComplexDensity P WF W E y)=
      (∫ y in Y,scalarFirstLeadingComplexDensity P E y)+(∫ y in Y,scalarFirstJetComplexDensity P WF E y)+
        (∫ y in Y,scalarFirstDefectComplexDensity P WF W E y) := by
    calc
      _ = ∫ y in Y,scalarFirstLeadingComplexDensity P E y+scalarFirstJetComplexDensity P WF E y+
        scalarFirstDefectComplexDensity P WF W E y := integral_congr_ae hEq
      _ = _ := (integral_add (hL.1.add hJ.1) hF.1).trans
        (congrArg (fun r => r+(∫ y in Y,scalarFirstDefectComplexDensity P WF W E y)) (integral_add hL.1 hJ.1))
  refine ⟨hInt,?_⟩
  rw [hIntegral]
  have hε1 : ε ≤ 1 := hSmall.trans ((min_le_left _ _).trans hηL1)
  calc
    _ ≤ |(∫ y in Y,scalarFirstLeadingComplexDensity P E y)+(∫ y in Y,scalarFirstJetComplexDensity P WF E y)|+
        |∫ y in Y,scalarFirstDefectComplexDensity P WF W E y| := abs_add_le _ _
    _ ≤ |∫ y in Y,scalarFirstLeadingComplexDensity P E y|+|∫ y in Y,scalarFirstJetComplexDensity P WF E y|+
        |∫ y in Y,scalarFirstDefectComplexDensity P WF W E y| := add_le_add (abs_add_le _ _) le_rfl
    _ ≤ CL*ε^2*energySq Y d.γ d.frame d.radius φ+CJ*ε^2*energySq Y d.γ d.frame d.radius φ+
        CF0*ε^2*energySq Y d.γ d.frame d.radius φ := add_le_add (add_le_add hL.2 hJ.2) hF.2
    _ = C*ε^2*energySq Y d.γ d.frame d.radius φ := by dsimp only [C];ring
    _ ≤ _ := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (by nlinarith only [hε,hε1] : ε^2 ≤ ε) hC)
      (energySq_nonneg _ _ _ _ _)

end ShrinkingSpheres.ParallelEnergy
