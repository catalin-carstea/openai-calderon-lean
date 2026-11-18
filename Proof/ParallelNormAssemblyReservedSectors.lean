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
open OAI.AnisotropicCalderon.SphereHarmonic

variable {Y : Set X} {d : Data} {CF CT CB CS CG CK ε : ℝ}

/-- Corrected model cross with respectively scalar, first or potential.
The model partner is actual lowering minus the SAME genuine defect. -/
def componentCorrectedModelSectorDensity (P : PhysicalPrincipalData Y d CF CT)
    (WF : PhysicalFirstCommutatorPacket P CB CS ε)
    (W : ∀ y ∈ Y,PhysicalPotentialQuarticData P y CG CK)
    (G : X × X → ℝ) (hG : ContDiff ℝ ∞ G) (T L : X → SphereL2)
    (k : Fin 3) (y : X) : ℝ :=
  let U := ambientHigherSobolevSection (5/2:ℝ) (by norm_num) G hG
  let Z := sphereSobolevZeroEquiv orthogonalSphereHarmonics denseSphereHarmonics
  let j : Fin 4 := ⟨k.val,by omega⟩
  4*metricDensity d.γ y*(⟪Z (T y),componentForwardOutputs P W U T j y⟫_ℝ-
    ⟪Z (L y)-sphereSobolevInclusionL (5/2:ℝ) 0 (by norm_num) (componentDefectSource d G hG y),
      componentAdjointOutputs P WF W U L j y⟫_ℝ)

def correctedModelSectorComplexDensity (P : PhysicalPrincipalData Y d CF CT)
    (WF : PhysicalFirstCommutatorPacket P CB CS ε)
    (W : ∀ y ∈ Y,PhysicalPotentialQuarticData P y CG CK)
    {φ : Field} (E : HarmonicTestExpansion Y d.γ d.frame φ) (D : AngularModelData E d.radius)
    (k : Fin 3) (y : X) : ℝ :=
  componentCorrectedModelSectorDensity P WF W (fun p => (E.representative p).re)
      (Complex.reCLM.contDiff.comp E.representativeSmooth)
      D.realComponent.raisingOutput D.realComponent.loweringOutput k y+
    componentCorrectedModelSectorDensity P WF W (fun p => (E.representative p).im)
      (Complex.imCLM.contDiff.comp E.representativeSmooth)
      D.imagComponent.raisingOutput D.imagComponent.loweringOutput k y

/-- New scalar-first author's exact corrected model/scalar assignment. -/
def correctedModelScalarComplexDensity (P : PhysicalPrincipalData Y d CF CT)
    (WF : PhysicalFirstCommutatorPacket P CB CS ε)
    (W : ∀ y ∈ Y,PhysicalPotentialQuarticData P y CG CK)
    {φ : Field} (E : HarmonicTestExpansion Y d.γ d.frame φ) (D : AngularModelData E d.radius) : X → ℝ :=
  correctedModelSectorComplexDensity P WF W E D 0

def correctedModelFirstComplexDensity (P : PhysicalPrincipalData Y d CF CT)
    (WF : PhysicalFirstCommutatorPacket P CB CS ε)
    (W : ∀ y ∈ Y,PhysicalPotentialQuarticData P y CG CK)
    {φ : Field} (E : HarmonicTestExpansion Y d.γ d.frame φ) (D : AngularModelData E d.radius) : X → ℝ :=
  correctedModelSectorComplexDensity P WF W E D 1

/-- Potential-containing sectors stay grouped, including their corrected
model/potential term. No separate smallness is asserted. -/
def correctedPotentialMixedComplexDensity (P : PhysicalPrincipalData Y d CF CT)
    (WF : PhysicalFirstCommutatorPacket P CB CS ε)
    (W : ∀ y ∈ Y,PhysicalPotentialQuarticData P y CG CK)
    {φ : Field} (E : HarmonicTestExpansion Y d.γ d.frame φ) (D : AngularModelData E d.radius) (y : X) : ℝ :=
  sectorComplexDensity P WF W E D 4 y+sectorComplexDensity P WF W E D 5 y+
    correctedModelSectorComplexDensity P WF W E D 2 y

/-- This author retains corrected model/first together with every
potential-containing term, preserving any cancellation across them. -/
def remainingCorrectedReservedDensity (P : PhysicalPrincipalData Y d CF CT)
    (WF : PhysicalFirstCommutatorPacket P CB CS ε)
    (W : ∀ y ∈ Y,PhysicalPotentialQuarticData P y CG CK)
    {φ : Field} (E : HarmonicTestExpansion Y d.γ d.frame φ) (D : AngularModelData E d.radius) (y : X) : ℝ :=
  correctedModelFirstComplexDensity P WF W E D y+correctedPotentialMixedComplexDensity P WF W E D y

/-- Exact new ownership split; no part of the complete defect was silently
removed, and the two retained mixed groups are not estimated separately. -/
theorem corrected_reserved_density_split (P : PhysicalPrincipalData Y d CF CT)
    (WF : PhysicalFirstCommutatorPacket P CB CS ε)
    (W : ∀ y ∈ Y,PhysicalPotentialQuarticData P y CG CK)
    {φ : Field} (E : HarmonicTestExpansion Y d.γ d.frame φ) (D : AngularModelData E d.radius) (y : X) :
    correctedReservedComplexDensity P WF W E D y=
      correctedModelScalarComplexDensity P WF W E D y+remainingCorrectedReservedDensity P WF W E D y := by
  simp only [correctedReservedComplexDensity,componentCorrectedReservedDensity,
    correctedModelScalarComplexDensity,remainingCorrectedReservedDensity,
    correctedModelFirstComplexDensity,correctedPotentialMixedComplexDensity,
    correctedModelSectorComplexDensity,componentCorrectedModelSectorDensity,
    sectorComplexDensity_eq_components,componentForwardOutputs,componentAdjointOutputs,
    PhysicalPrincipalData.truncatedCovariantCoreSection,PhysicalPrincipalData.truncatedFormalAdjointCore,
    HarmonicTestExpansion.realHigherSobolevSection,HarmonicTestExpansion.imagHigherSobolevSection,
    inner_add_right]
  ring

end ShrinkingSpheres.ParallelEnergy
