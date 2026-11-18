import Proof.ParallelNormAssemblyReservedDefect

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

variable {Y Ω : Set X} {m : ℕ} {K ρ c₀ floor ε CF CT CB CS CG CK : ℝ}
  {M : Fin (m+1) → ℝ} {Cj : Fin 9 → ℝ} {d : Data}

/-- The grouped remaining commutator form, with actual model adjoint
lowering-minus-defect. Scalar/potential and first/potential remain grouped. -/
def componentCorrectedReservedDensity (P : PhysicalPrincipalData Y d CF CT)
    (WF : PhysicalFirstCommutatorPacket P CB CS ε)
    (W : ∀ y ∈ Y,PhysicalPotentialQuarticData P y CG CK)
    (G : X × X → ℝ) (hG : ContDiff ℝ ∞ G) (T L : X → SphereL2) (y : X) : ℝ :=
  let U := ambientHigherSobolevSection (5/2:ℝ) (by norm_num) G hG
  let Z := sphereSobolevZeroEquiv orthogonalSphereHarmonics denseSphereHarmonics
  componentSectorDensity P WF W U T L 4 y+componentSectorDensity P WF W U T L 5 y+
    4*metricDensity d.γ y*(⟪Z (T y),P.truncatedCovariantCoreSection W U y⟫_ℝ-
      ⟪Z (L y)-sphereSobolevInclusionL (5/2:ℝ) 0 (by norm_num) (componentDefectSource d G hG y),
        P.truncatedFormalAdjointCore WF W U y⟫_ℝ)

def correctedReservedComplexDensity (P : PhysicalPrincipalData Y d CF CT)
    (WF : PhysicalFirstCommutatorPacket P CB CS ε)
    (W : ∀ y ∈ Y,PhysicalPotentialQuarticData P y CG CK)
    {φ : Field} (E : HarmonicTestExpansion Y d.γ d.frame φ) (D : AngularModelData E d.radius) (y : X) : ℝ :=
  componentCorrectedReservedDensity P WF W (fun p => (E.representative p).re)
      (Complex.reCLM.contDiff.comp E.representativeSmooth)
      D.realComponent.raisingOutput D.realComponent.loweringOutput y+
    componentCorrectedReservedDensity P WF W (fun p => (E.representative p).im)
      (Complex.imCLM.contDiff.comp E.representativeSmooth)
      D.imagComponent.raisingOutput D.imagComponent.loweringOutput y

lemma corrected_reserved_density_pointwise (P : PhysicalPrincipalData Y d CF CT)
    (WF : PhysicalFirstCommutatorPacket P CB CS ε)
    (W : ∀ y ∈ Y,PhysicalPotentialQuarticData P y CG CK)
    {φ : Field} (E : HarmonicTestExpansion Y d.γ d.frame φ) (D : AngularModelData E d.radius) (y : X) :
    correctedReservedComplexDensity P WF W E D y=
      reservedComplexDensity P WF W E D y+4*defectAdjointComplexDensity P WF W E y := by
  simp only [correctedReservedComplexDensity,componentCorrectedReservedDensity,reservedComplexDensity,
    sectorComplexDensity_eq_components,componentSectorDensity,weightedSquareSector,
    componentForwardOutputs,componentAdjointOutputs,defectAdjointComplexDensity,
    componentDefectAdjointPairing,PhysicalPrincipalData.truncatedCovariantCoreSection,
    PhysicalPrincipalData.truncatedFormalAdjointCore,HarmonicTestExpansion.realHigherSobolevSection,
    HarmonicTestExpansion.imagHigherSobolevSection,inner_add_right,inner_sub_left]
  ring

theorem reserved_density_integrable (P : PhysicalPrincipalData Y d CF CT)
    (hY : IsOpen Y) (hΩ : IsOpen Ω) (hSub : Y ⊆ Ω)
    (hd : Admissible Y Ω K ρ c₀ M Cj floor ε d) (hK : 0 < K)
    (WF : PhysicalFirstCommutatorPacket P CB CS ε)
    (W : ∀ y ∈ Y,PhysicalPotentialQuarticData P y CG CK) (hCG : 0 ≤ CG) (hCK : 0 ≤ CK)
    {φ : Field} (E : HarmonicTestExpansion Y d.γ d.frame φ) (D : AngularModelData E d.radius) :
    IntegrableOn (reservedComplexDensity P WF W E D) Y :=
  compressedComplexDensity_integrable P hY hΩ hSub hd hK WF W hCG hCK E D 4

/-- Exact integrated reduction to the corrected physical commutator and
FOUR times the already bounded complete residual/model-defect density. -/
theorem reserved_integral_corrected_defect_identity (P : PhysicalPrincipalData Y d CF CT)
    (hY : IsOpen Y) (hΩ : IsOpen Ω) (hSub : Y ⊆ Ω)
    (hd : Admissible Y Ω K ρ c₀ M Cj floor ε d) (hK : 0 < K)
    (WF : PhysicalFirstCommutatorPacket P CB CS ε)
    (W : ∀ y ∈ Y,PhysicalPotentialQuarticData P y CG CK) (hCG : 0 ≤ CG) (hCK : 0 ≤ CK)
    {φ : Field} (E : HarmonicTestExpansion Y d.γ d.frame φ) (D : AngularModelData E d.radius) :
    IntegrableOn (correctedReservedComplexDensity P WF W E D) Y ∧
      (∫ y in Y,reservedComplexDensity P WF W E D y)=
        (∫ y in Y,correctedReservedComplexDensity P WF W E D y)-
          4*(∫ y in Y,P.modelDefectResidualDensity E y) := by
  have hR := reserved_density_integrable P hY hΩ hSub hd hK WF W hCG hCK E D
  have hD := defect_complex_pairing_integral_eq P hY hΩ hSub hd hK WF W hCG hCK E
  have hEq : correctedReservedComplexDensity P WF W E D =ᵐ[volume.restrict Y]
      (fun y => reservedComplexDensity P WF W E D y+4*defectAdjointComplexDensity P WF W E y) :=
    Eventually.of_forall (corrected_reserved_density_pointwise P WF W E D)
  have hI : IntegrableOn (correctedReservedComplexDensity P WF W E D) Y :=
    (hR.add (hD.1.const_mul 4)).congr hEq.symm
  refine ⟨hI,?_⟩
  have hh : (∫ y in Y,correctedReservedComplexDensity P WF W E D y)=
      (∫ y in Y,reservedComplexDensity P WF W E D y)+4*(∫ y in Y,P.modelDefectResidualDensity E y) := by
    calc
      _ = ∫ y in Y,reservedComplexDensity P WF W E D y+4*defectAdjointComplexDensity P WF W E y :=
        integral_congr_ae hEq
      _ = _ := by rw [integral_add hR (hD.1.const_mul 4),integral_const_mul,hD.2]
  linarith only [hh]

/-- The exact model-defect pairing itself has the original uniform bound,
for ANY coherent fixed first and potential packet before tests. -/
theorem uniform_defect_adjoint_complex_integral_bound
    (hY : IsOpen Y) (hΩ : IsOpen Ω) (hSub : Y ⊆ Ω) (hm : 10 ≤ m)
    (K ρ c₀ : ℝ) (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ) (hK : 1 ≤ K) (hρ : 0 < ρ)
    (CF CT CB CS CG CK : ℝ) (hCG : 0 ≤ CG) (hCK : 0 ≤ CK) :
    ∃ η C : ℝ,0 < η ∧ η ≤ 1 ∧ 0 ≤ C ∧
    ∀ floor,1 ≤ floor → ∀ ε,0 ≤ ε → ε ≤ η → ∀ d,
    Admissible Y Ω K ρ c₀ M Cj floor ε d → ∀ P : PhysicalPrincipalData Y d CF CT,
    ∀ WF : PhysicalFirstCommutatorPacket P CB CS ε,
    ∀ W : ∀ y ∈ Y,PhysicalPotentialQuarticData P y CG CK,
    ∀ φ,Test Y d.γ d.frame φ →
    ∀ (E : HarmonicTestExpansion Y d.γ d.frame φ) (D : AngularModelData E d.radius),
      IntegrableOn (defectAdjointComplexDensity P WF W E) Y ∧
      |∫ y in Y,defectAdjointComplexDensity P WF W E y| ≤ C*ε*energySq Y d.γ d.frame d.radius φ := by
  obtain ⟨η,C,hη,hη1,hC,hBase⟩ := uniform_physical_model_defect_residual_integral_bound
    hY hΩ hSub hm K ρ c₀ M Cj hK hρ CF
  refine ⟨η,C,hη,hη1,hC,?_⟩
  intro floor hf ε hε hSmall d hd P WF W φ hφ E D
  have hActual := defect_complex_pairing_integral_eq P hY hΩ hSub hd (zero_lt_one.trans_le hK) WF W hCG hCK E
  refine ⟨hActual.1,?_⟩
  rw [hActual.2]
  exact (hBase floor hf ε hε hSmall d hd CT P φ E D hφ).2

end ShrinkingSpheres.ParallelEnergy
