import Proof.ParallelNormAssemblyReservedModel

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

/-- The remaining quantitative corrected commutator, with all five mixed
sectors still grouped and genuine model adjoint lowering-minus-defect. -/
def UniformCorrectedReservedEstimate (Y Ω : Set X) {m : ℕ}
    (K ρ c₀ : ℝ) (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ) (CF CT : ℝ) : Prop :=
  ∀ CB CS CG CK : ℝ,0 ≤ CB → 0 ≤ CS → 0 ≤ CG → 0 ≤ CK →
    ∃ B η C : ℝ,0 < η ∧ η ≤ 1 ∧ 0 ≤ C ∧
    ∀ floor,B ≤ floor → ∀ ε,0 ≤ ε → ε ≤ η → ∀ d,
    Admissible Y Ω K ρ c₀ M Cj floor ε d → ∀ P : PhysicalPrincipalData Y d CF CT,
    ∀ WF : PhysicalFirstCommutatorPacket P CB CS ε,
    ∀ W : ∀ y ∈ Y,PhysicalPotentialQuarticData P y CG CK,
    ∀ φ,Test Y d.γ d.frame φ →
    ∀ (E : HarmonicTestExpansion Y d.γ d.frame φ) (D : AngularModelData E d.radius),
      |∫ y in Y,correctedReservedComplexDensity P WF W E D y| ≤
        C*ε*energySq Y d.γ d.frame d.radius φ

/-- Checked uniform caller discharging the complete defect contribution
through its existing actual physical estimate. The corrected grouped
commutator estimate is explicitly open, not silently assumed proved. -/
theorem uniform_reserved_complex_density_integral_bound_of_corrected
    {Y Ω : Set X} (hY : IsOpen Y) (hΩ : IsOpen Ω) (hSub : Y ⊆ Ω)
    {m : ℕ} (hm : 10 ≤ m) (K ρ c₀ : ℝ) (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ)
    (hK : 1 ≤ K) (hρ : 0 < ρ) (CF CT : ℝ)
    (hCorrected : UniformCorrectedReservedEstimate Y Ω K ρ c₀ M Cj CF CT) :
    ∀ CB CS CG CK : ℝ,0 ≤ CB → 0 ≤ CS → 0 ≤ CG → 0 ≤ CK →
    ∃ B η C : ℝ,0 < η ∧ η ≤ 1 ∧ 0 ≤ C ∧
    ∀ floor,B ≤ floor → ∀ ε,0 ≤ ε → ε ≤ η → ∀ d,
    Admissible Y Ω K ρ c₀ M Cj floor ε d → ∀ P : PhysicalPrincipalData Y d CF CT,
    ∀ WF : PhysicalFirstCommutatorPacket P CB CS ε,
    ∀ W : ∀ y ∈ Y,PhysicalPotentialQuarticData P y CG CK,
    ∀ φ,Test Y d.γ d.frame φ →
    ∀ (E : HarmonicTestExpansion Y d.γ d.frame φ) (D : AngularModelData E d.radius),
      IntegrableOn (reservedComplexDensity P WF W E D) Y ∧
      |∫ y in Y,reservedComplexDensity P WF W E D y| ≤
        C*ε*energySq Y d.γ d.frame d.radius φ := by
  obtain ⟨ηD,CD,hηD,hηD1,hCD,hDefect⟩ := uniform_physical_model_defect_residual_integral_bound
    hY hΩ hSub hm K ρ c₀ M Cj hK hρ CF
  intro CB CS CG CK hCB hCS hCG hCK
  obtain ⟨B,ηC,CC,hηC,hηC1,hCC,hComm⟩ := hCorrected CB CS CG CK hCB hCS hCG hCK
  refine ⟨max 1 B,min ηD ηC,CC+4*CD,lt_min hηD hηC,(min_le_left _ _).trans hηD1,
    by positivity,?_⟩
  intro floor hf ε hε hSmall d hd P WF W φ hφ E D
  have hf1 := (le_max_left 1 B).trans hf
  have hfB := (le_max_right 1 B).trans hf
  have hR := reserved_density_integrable P hY hΩ hSub hd (zero_lt_one.trans_le hK) WF W hCG hCK E D
  have hEq := reserved_integral_corrected_defect_identity P hY hΩ hSub hd (zero_lt_one.trans_le hK) WF W hCG hCK E D
  have hC := hComm floor hfB ε hε (hSmall.trans (min_le_right _ _)) d hd P WF W φ hφ E D
  have hD := (hDefect floor hf1 ε hε (hSmall.trans (min_le_left _ _)) d hd CT P φ E D hφ).2
  refine ⟨hR,?_⟩
  rw [hEq.2]
  calc
    _ ≤ |∫ y in Y,correctedReservedComplexDensity P WF W E D y|+
        |4*(∫ y in Y,P.modelDefectResidualDensity E y)| := abs_sub _ _
    _ = |∫ y in Y,correctedReservedComplexDensity P WF W E D y|+
        4*|∫ y in Y,P.modelDefectResidualDensity E y| := by rw [abs_mul,abs_of_pos (by norm_num : (0:ℝ)<4)]
    _ ≤ CC*ε*energySq Y d.γ d.frame d.radius φ+4*(CD*ε*energySq Y d.γ d.frame d.radius φ) :=
      add_le_add hC (mul_le_mul_of_nonneg_left hD (by norm_num))
    _ = _ := by ring

end ShrinkingSpheres.ParallelEnergy
