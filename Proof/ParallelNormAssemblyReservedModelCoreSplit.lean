import Proof.ParallelNormAssemblyReservedModelZeroAdjoint
import Proof.ParallelScalarModelIdentity

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2800000
set_option maxRecDepth 10000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter
open scoped ContDiff Topology InnerProductSpace
namespace ShrinkingSpheres.ParallelEnergy
open OAI.AnisotropicCalderon.SphereHarmonic OAI.AnisotropicCalderon.DirichletFamily

variable {Y : Set X} {d : Data} {CF CT CG CK : ℝ}

def modelPotentialCorrectedCoreDensity (P : PhysicalPrincipalData Y d CF CT)
    (W : ∀ y ∈ Y,PhysicalPotentialQuarticData P y CG CK)
    (U : X → SphereSobolev (5/2:ℝ)) (y : X) : ℝ :=
  4*metricDensity d.γ y*(⟪modelRaisingSection d (fiveHalfToTwoSection U) y,P.potentialQuadraticCoreSection W U y⟫_ℝ-
    ⟪modelLoweringSection d (fiveHalfToTwoSection U) y-modelAdjointDefectSection d (fiveHalfToTwoSection U) y,
      P.potentialQuadraticAdjointCoreSection W U y⟫_ℝ)

def modelPotentialLeadingCoreDensity (P : PhysicalPrincipalData Y d CF CT)
    (W : ∀ y ∈ Y,PhysicalPotentialQuarticData P y CG CK)
    (U : X → SphereSobolev (5/2:ℝ)) (y : X) : ℝ :=
  4*metricDensity d.γ y*∑ i : I,(
    ⟪flatRaisingSobolevL 1 i (highSectionCovariantDerivative d (fiveHalfToTwoSection U) y (d.frame y i)),
      P.potentialQuadraticCoreSection W U y⟫_ℝ+
    ⟪flatLoweringSobolevL 1 i (highSectionCovariantDerivative d (fiveHalfToTwoSection U) y (d.frame y i)),
      P.potentialQuadraticAdjointCoreSection W U y⟫_ℝ)

def modelPotentialZeroCoreDensity (P : PhysicalPrincipalData Y d CF CT)
    (W : ∀ y ∈ Y,PhysicalPotentialQuarticData P y CG CK)
    (U : X → SphereSobolev (5/2:ℝ)) (y : X) : ℝ := by
  classical
  exact if hy : y ∈ Y then 4*metricDensity d.γ y*(
    ⟪modelZeroForwardCoreValue P (W y hy) (U y),P.potentialQuadraticCoreL (W y hy) (U y)⟫_ℝ-
    ⟪modelZeroAdjointCoreValue P (W y hy) (U y),P.potentialQuadraticAdjointCoreL (W y hy) (U y)⟫_ℝ) else 0

/-- Exact literal model/potential split into its two leading orientations
and the complete raising/degree versus degree-minus-one angular pair. -/
theorem model_potential_corrected_core_split (P : PhysicalPrincipalData Y d CF CT)
    (W : ∀ y ∈ Y,PhysicalPotentialQuarticData P y CG CK)
    (Q : SmoothCoefficientJets 2)
    (hQ : ∀ z ∈ Metric.closedBall (0:X) 1,coefficientValue 2 Q =ᶠ[𝓝 z] (fun _ => (1:ℝ)))
    (U : X → SphereSobolev (5/2:ℝ)) {y : X} (hy : y ∈ Y) :
    modelPotentialCorrectedCoreDensity P W U y=
      modelPotentialLeadingCoreDensity P W U y+modelPotentialZeroCoreDensity P W U y := by
  have hR : modelRaisingSection d (fiveHalfToTwoSection U) y=
      (∑ i : I,flatRaisingSobolevL 1 i (highSectionCovariantDerivative d (fiveHalfToTwoSection U) y (d.frame y i)))+
        modelZeroForwardCoreValue P (W y hy) (U y) := by
    rw [model_zero_forward_actual P hy (W y hy)]
    simp only [modelRaisingSection,highSectionModelPlus,map_add,map_smul,Finset.sum_add_distrib,fiveHalfToTwoSection,flatOneRaisingL,modelLogRadiusCoefficient]
  have hA : modelLoweringSection d (fiveHalfToTwoSection U) y-modelAdjointDefectSection d (fiveHalfToTwoSection U) y=
      -(∑ i : I,flatLoweringSobolevL 1 i (highSectionCovariantDerivative d (fiveHalfToTwoSection U) y (d.frame y i)))+
        modelZeroAdjointCoreValue P (W y hy) (U y) := by
    rw [scalar_model_corrected_lowering_coarse_sum,model_zero_adjoint_actual P hy (W y hy) Q hQ]
    simp only [map_add,map_neg,map_smul,Finset.sum_add_distrib,Finset.sum_neg_distrib,fiveHalfToTwoSection,
      sphereSobolevInclusionL_trans_apply]
  simp only [modelPotentialCorrectedCoreDensity,modelPotentialLeadingCoreDensity,modelPotentialZeroCoreDensity,
    dite_eq_left hy,hR,hA,inner_add_left,inner_neg_left,sum_inner,Finset.sum_add_distrib,
    PhysicalPrincipalData.potentialQuadraticCoreSection,PhysicalPrincipalData.potentialQuadraticAdjointCoreSection]
  ring

/-- The original selected model outputs give exactly this corrected
physical model/potential density, including its original factor four. -/
theorem component_corrected_model_potential_eq {Ω : Set X} {m : ℕ}
    {K ρ c₀ floor ε CB CS : ℝ} {M : Fin (m+1) → ℝ} {Cj : Fin 9 → ℝ}
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
      (L.contDiff.comp E.representativeSmooth) C.raisingOutput C.loweringOutput 2 y=
      modelPotentialCorrectedCoreDensity P W
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
    modelPotentialCorrectedCoreDensity,ambient_fiveHalfToTwoSection]
  rw [hR,hL]

end ShrinkingSpheres.ParallelEnergy
