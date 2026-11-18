import Proof.ParallelScalarModelIdentity
import Proof.ParallelNormAssemblyReservedParts

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2800000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
open Set Filter
open scoped ContDiff Topology InnerProductSpace
namespace ShrinkingSpheres.ParallelEnergy
open OAI.AnisotropicCalderon.SphereHarmonic OAI.AnisotropicCalderon.DirichletFamily

variable {Y : Set X} {d : Data} {CF CT CB CS CG CK ε : ℝ}

def modelFirstCorrectedDensity (P : PhysicalPrincipalData Y d CF CT)
    (WF : PhysicalFirstCommutatorPacket P CB CS ε)
    (W : ∀ y ∈ Y,PhysicalPotentialQuarticData P y CG CK)
    (U : X → SphereSobolev (5/2:ℝ)) (y : X) : ℝ :=
  let U2 := fiveHalfToTwoSection U;
  4*metricDensity d.γ y*(⟪modelRaisingSection d U2 y,P.firstCovariantCoreSection U2 y⟫_ℝ-
    ⟪modelLoweringSection d U2 y-modelAdjointDefectSection d U2 y,P.firstFormalAdjointCore WF W U y⟫_ℝ)

def modelFirstCorrectedComplexDensity (P : PhysicalPrincipalData Y d CF CT)
    (WF : PhysicalFirstCommutatorPacket P CB CS ε)
    (W : ∀ y ∈ Y,PhysicalPotentialQuarticData P y CG CK)
    {φ : Field} (E : HarmonicTestExpansion Y d.γ d.frame φ) (y : X) : ℝ :=
  modelFirstCorrectedDensity P WF W (E.realHigherSobolevSection (5/2:ℝ) (by norm_num)) y+
    modelFirstCorrectedDensity P WF W (E.imagHigherSobolevSection (5/2:ℝ) (by norm_num)) y

/-- Both literal first-sector orientations use the SAME actual model
source and COMPLETE effective first core, with its original fixed WF/W. -/
theorem component_corrected_model_first_eq {Ω : Set X} {m : ℕ}
    {K ρ c₀ floor : ℝ} {M : Fin (m+1) → ℝ} {Cj : Fin 9 → ℝ}
    (hY : IsOpen Y) (hSub : Y ⊆ Ω)
    (hd : Admissible Y Ω K ρ c₀ M Cj floor ε d) (hK : 0 < K)
    (P : PhysicalPrincipalData Y d CF CT) (WF : PhysicalFirstCommutatorPacket P CB CS ε)
    (W : ∀ y ∈ Y,PhysicalPotentialQuarticData P y CG CK)
    (Q : SmoothCoefficientJets 2)
    (hQ : ∀ z ∈ Metric.closedBall (0:X) 1,coefficientValue 2 Q =ᶠ[𝓝 z] (fun _ => (1:ℝ)))
    {φ : Field} (E : HarmonicTestExpansion Y d.γ d.frame φ) (L : ℂ →L[ℝ] ℝ)
    (C : AngularComponentData E d.radius L) (hφ : smoothNear φ (bundle Y d.γ))
    {y : X} (hy : y ∈ Y) :
    componentCorrectedModelSectorDensity P WF W (fun p => L (E.representative p))
      (L.contDiff.comp E.representativeSmooth) C.raisingOutput C.loweringOutput 1 y=
    modelFirstCorrectedDensity P WF W
      (ambientHigherSobolevSection (5/2:ℝ) (by norm_num) (fun p => L (E.representative p))
        (L.contDiff.comp E.representativeSmooth)) y := by
  let G := fun p => L (E.representative p)
  let hG := L.contDiff.comp E.representativeSmooth
  let U2 := ambientSobolevSection 2 (by norm_num) G hG
  let Z := sphereSobolevZeroEquiv orthogonalSphereHarmonics denseSphereHarmonics
  have hg : Elliptic Y K d.γ :=
    ⟨fun i j => (hd.1.1.1 i j).mono hSub,fun x hx => hd.1.1.2 x (hSub hx)⟩
  have he (i : I) : ContDiffOn ℝ ∞ (fun x => d.frame x i) Y := (hd.1.2.2.2.2.2.2.1 i).mono hSub
  have hFrame (x : X) (hx : x ∈ Y) := hd.1.2.2.2.2.2.2.2 x (hSub hx)
  have hR : Z (C.raisingOutput y)=modelRaisingSection d U2 y := by
    have hh := congrArg Z (C.canonical_raising_section_eq hY hg hK he hFrame hφ Q hQ hy)
    simpa only [Z,LinearIsometryEquiv.apply_symm_apply,modelRaisingSection,U2,G,hG] using hh.symm
  have hL := corrected_lowering_output_eq hY hSub hd hK Q hQ E L C hφ hy
  simp only [componentCorrectedModelSectorDensity,componentForwardOutputs,componentAdjointOutputs,
    modelFirstCorrectedDensity,ambient_fiveHalfToTwoSection]
  rw [hR,hL]

/-- Literal real-plus-imaginary corrected model/first density matches its
intrinsic actual-model expression; all original packets stay fixed. -/
theorem correctedModelFirstComplexDensity_eq {Ω : Set X} {m : ℕ}
    {K ρ c₀ floor : ℝ} {M : Fin (m+1) → ℝ} {Cj : Fin 9 → ℝ}
    (hY : IsOpen Y) (hSub : Y ⊆ Ω)
    (hd : Admissible Y Ω K ρ c₀ M Cj floor ε d) (hK : 0 < K)
    (P : PhysicalPrincipalData Y d CF CT) (WF : PhysicalFirstCommutatorPacket P CB CS ε)
    (W : ∀ y ∈ Y,PhysicalPotentialQuarticData P y CG CK)
    {φ : Field} (E : HarmonicTestExpansion Y d.γ d.frame φ) (D : AngularModelData E d.radius)
    (hφ : smoothNear φ (bundle Y d.γ)) {y : X} (hy : y ∈ Y) :
    correctedModelFirstComplexDensity P WF W E D y=modelFirstCorrectedComplexDensity P WF W E y := by
  obtain ⟨Q,hQ⟩ := exists_unit_boundary_coefficient
  have hr := component_corrected_model_first_eq hY hSub hd hK P WF W Q hQ E Complex.reCLM D.realComponent hφ hy
  have hi := component_corrected_model_first_eq hY hSub hd hK P WF W Q hQ E Complex.imCLM D.imagComponent hφ hy
  exact congrArg₂ (fun x y : ℝ => x+y) hr hi

end ShrinkingSpheres.ParallelEnergy
