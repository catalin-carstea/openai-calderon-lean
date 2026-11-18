import Proof.ParallelScalarModelIdentity
import Proof.PhysicalScalarCoreDomain

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2800000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
open Set Filter MeasureTheory
open scoped ContDiff Topology InnerProductSpace
namespace ShrinkingSpheres.ParallelEnergy
open OAI.AnisotropicCalderon.SphereHarmonic

/-- Both corrected orientations are qualitatively integrable on the SAME
supported smooth core before any integral cancellation is performed. -/
theorem scalarModelCorrectedDensity_integrableOn
    {Y Ω : Set X} {m : ℕ} {K ρ c₀ floor ε : ℝ}
    {M : Fin (m+1) → ℝ} {Cj : Fin 9 → ℝ} {d : Data}
    (hY : IsOpen Y) (hSub : Y ⊆ Ω)
    (hd : Admissible Y Ω K ρ c₀ M Cj floor ε d) (hK : 0 < K)
    (U : X → SphereSobolev (5/2:ℝ)) (hU : ContDiff ℝ ∞ U)
    (S : Set X) (hS : IsCompact S) (hSY : S ⊆ Y) (h0U : ∀ x ∉ S,U x=0) :
    IntegrableOn (scalarModelCorrectedDensity d U) Y := by
  let U2 := fiveHalfToTwoSection U
  have hU2 : ContDiff ℝ ∞ U2 := (sphereSobolevInclusionL (5/2:ℝ) 2 (by norm_num)).contDiff.comp hU
  have h02 (x : X) (hx : x ∉ S) : U2 x=0 := by simp only [U2,fiveHalfToTwoSection,h0U x hx,map_zero]
  have hg : Elliptic Y K d.γ :=
    ⟨fun i j => (hd.1.1.1 i j).mono hSub,fun x hx => hd.1.1.2 x (hSub hx)⟩
  have he (i : I) : ContDiffOn ℝ ∞ (fun x => d.frame x i) Y := (hd.1.2.2.2.2.2.2.1 i).mono hSub
  have hlog : ContDiffOn ℝ ∞ (fun x => Real.log (d.radius x)) Y :=
    hd.2.2.2.2.1.1.log (fun x hx => (hd.2.2.2.2.1.2 x hx).1.ne')
  have hModel := contDiff_supported_modelCovariantSections hY d hg hK he hlog U2 hU2 S hS.isClosed hSY h02
  have hScalar := physical_scalar_principal_core_supported hY hSub hd hK U2 hU2 S hS.isClosed hSY h02
  have hModelAdj := hModel.2.1.sub hModel.2.2
  have hMu (x : X) (hx : x ∈ S) := (hg.contDiffOn_density hK).contDiffAt (hY.mem_nhds (hSY hx))
  have hI : Integrable (fun x => metricDensity d.γ x*
      ⟪modelRaisingSection d U2 x,scalarCovariantSecondSection d (scalarPrincipalMatrix d.γ d.g₂ d.radius) U2 x⟫_ℝ) :=
    OperatorForms.integrable_local_weighted_operator_pair (innerSL ℝ) (metricDensity d.γ)
      (modelRaisingSection d U2) (scalarCovariantSecondSection d (scalarPrincipalMatrix d.γ d.g₂ d.radius) U2)
      (fun _ => ContinuousLinearMap.id ℝ (SphereSobolev 0)) S hS hMu hModel.1 hScalar.1.1 hScalar.1.2
      (fun _ _ => contDiffAt_const)
  have hJ : Integrable (fun x => metricDensity d.γ x*
      ⟪modelLoweringSection d U2 x-modelAdjointDefectSection d U2 x,
        scalarCovariantSecondTransposeSection d (metricDensity d.γ) (scalarPrincipalMatrix d.γ d.g₂ d.radius) U2 x⟫_ℝ) :=
    OperatorForms.integrable_local_weighted_operator_pair (innerSL ℝ) (metricDensity d.γ)
      (fun x => modelLoweringSection d U2 x-modelAdjointDefectSection d U2 x)
      (scalarCovariantSecondTransposeSection d (metricDensity d.γ) (scalarPrincipalMatrix d.γ d.g₂ d.radius) U2)
      (fun _ => ContinuousLinearMap.id ℝ (SphereSobolev 0)) S hS hMu hModelAdj hScalar.2.1 hScalar.2.2
      (fun _ _ => contDiffAt_const)
  apply (((hI.sub hJ).const_mul 4).integrableOn).congr
  exact Eventually.of_forall (fun x => by simp only [scalarModelCorrectedDensity,U2,Pi.sub_apply];ring)

theorem correctedModelScalarComplexDensity_integrableOn
    {Y Ω : Set X} {m : ℕ} {K ρ c₀ floor ε CF CT CB CS CG CK : ℝ}
    {M : Fin (m+1) → ℝ} {Cj : Fin 9 → ℝ} {d : Data}
    (hY : IsOpen Y) (hSub : Y ⊆ Ω)
    (hd : Admissible Y Ω K ρ c₀ M Cj floor ε d) (hK : 0 < K)
    (P : PhysicalPrincipalData Y d CF CT) (WF : PhysicalFirstCommutatorPacket P CB CS ε)
    (W : ∀ y ∈ Y,PhysicalPotentialQuarticData P y CG CK)
    {φ : Field} (E : HarmonicTestExpansion Y d.γ d.frame φ) (D : AngularModelData E d.radius)
    (hφ : smoothNear φ (bundle Y d.γ)) :
    IntegrableOn (correctedModelScalarComplexDensity P WF W E D) Y := by
  have hr := scalarModelCorrectedDensity_integrableOn hY hSub hd hK
    (E.realHigherSobolevSection (5/2:ℝ) (by norm_num)) (E.contDiff_realHigherSobolevSection _ _)
    E.supportSet E.compactSupportSet E.supportSubset (fun x hx => E.realHigherSobolevSection_zero _ _ (by norm_num) hx)
  have hi := scalarModelCorrectedDensity_integrableOn hY hSub hd hK
    (E.imagHigherSobolevSection (5/2:ℝ) (by norm_num)) (E.contDiff_imagHigherSobolevSection _ _)
    E.supportSet E.compactSupportSet E.supportSubset (fun x hx => E.imagHigherSobolevSection_zero _ _ (by norm_num) hx)
  apply (hr.add hi).congr
  filter_upwards [ae_restrict_mem hY.measurableSet] with x hx
  exact (correctedModelScalarComplexDensity_eq hY hSub hd hK P WF W E D hφ hx).symm

end ShrinkingSpheres.ParallelEnergy
