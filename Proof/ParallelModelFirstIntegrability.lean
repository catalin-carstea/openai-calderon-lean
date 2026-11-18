import Proof.ParallelModelFirstIdentity
import Proof.ParallelScalarFirstIntegrability

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

theorem modelFirstCorrectedDensity_integrableOn
    {Y Ω : Set X} {m : ℕ} {K ρ c₀ floor ε CF CT CB CS CG CK : ℝ}
    {M : Fin (m+1) → ℝ} {Cj : Fin 9 → ℝ} {d : Data}
    (hY : IsOpen Y) (hΩ : IsOpen Ω) (hSub : Y ⊆ Ω)
    (hd : Admissible Y Ω K ρ c₀ M Cj floor ε d) (hK : 0 < K)
    (P : PhysicalPrincipalData Y d CF CT) (WF : PhysicalFirstCommutatorPacket P CB CS ε)
    (W : ∀ y ∈ Y,PhysicalPotentialQuarticData P y CG CK) (hCG : 0 ≤ CG) (hCK : 0 ≤ CK)
    (U : X → SphereSobolev (5/2:ℝ)) (hU : ContDiff ℝ ∞ U)
    (S : Set X) (hS : IsCompact S) (hSY : S ⊆ Y) (h0U : ∀ x ∉ S,U x=0) :
    IntegrableOn (modelFirstCorrectedDensity P WF W U) Y := by
  let U2 := fiveHalfToTwoSection U
  have hU2 : ContDiff ℝ ∞ U2 := (sphereSobolevInclusionL (5/2:ℝ) 2 (by norm_num)).contDiff.comp hU
  have h02 (x : X) (hx : x ∉ S) : U2 x=0 := by simp only [U2,fiveHalfToTwoSection,h0U x hx,map_zero]
  have hg : Elliptic Y K d.γ :=
    ⟨fun i j => (hd.1.1.1 i j).mono hSub,fun x hx => hd.1.1.2 x (hSub hx)⟩
  have he (i : I) : ContDiffOn ℝ ∞ (fun x => d.frame x i) Y := (hd.1.2.2.2.2.2.2.1 i).mono hSub
  have hlog : ContDiffOn ℝ ∞ (fun x => Real.log (d.radius x)) Y :=
    hd.2.2.2.2.1.1.log (fun x hx => (hd.2.2.2.2.1.2 x hx).1.ne')
  have hModels := contDiff_supported_modelCovariantSections hY d hg hK he hlog U2 hU2 S hS.isClosed hSY h02
  have hM0 (x : X) (hx : x ∉ S) := modelCovariantSections_zero_off d U2 S hS.isClosed h02 x hx
  have hRaiseLp : MemLp (modelRaisingSection d U2) 2 (volume.restrict Y) :=
    hModels.1.continuous.memLp_of_hasCompactSupport (HasCompactSupport.intro hS (fun x hx => (hM0 x hx).1))
  have hAdjLp : MemLp (fun x => modelLoweringSection d U2 x-modelAdjointDefectSection d U2 x) 2 (volume.restrict Y) :=
    (hModels.2.1.sub hModels.2.2).continuous.memLp_of_hasCompactSupport
      (HasCompactSupport.intro hS (fun x hx => by rw [(hM0 x hx).2.1,(hM0 x hx).2.2,sub_self]))
  have hw := hd.contDiffOn_scalarPrincipalConnectionWeight hY hSub hK
  have hFirst := P.firstCovariantCoreSection_memLp hY hΩ hSub hd hK U2 hU2 S hS hSY h02 hw 2
  have hFirstAdj := P.firstFormalAdjointCore_memLp hY hΩ hSub hd hK WF W hCG hCK U hU S hS hSY h0U hw 2
  have hForward := integrableOn_local_weighted_inner_of_memLp hY.measurableSet hS hSY _ _ hRaiseLp hFirst
    (fun x _ hx => (hM0 x hx).1) _ (hg.contDiffOn_density hK).continuousOn
  have hBackward := integrableOn_local_weighted_inner_of_memLp hY.measurableSet hS hSY _ _ hAdjLp hFirstAdj
    (fun x _ hx => by rw [(hM0 x hx).2.1,(hM0 x hx).2.2,sub_self]) _ (hg.contDiffOn_density hK).continuousOn
  apply ((hForward.sub hBackward).const_mul 4).congr
  exact Eventually.of_forall (fun x => by simp only [modelFirstCorrectedDensity,U2,Pi.sub_apply];ring)

theorem correctedModelFirstComplexDensity_integrableOn
    {Y Ω : Set X} {m : ℕ} {K ρ c₀ floor ε CF CT CB CS CG CK : ℝ}
    {M : Fin (m+1) → ℝ} {Cj : Fin 9 → ℝ} {d : Data}
    (hY : IsOpen Y) (hΩ : IsOpen Ω) (hSub : Y ⊆ Ω)
    (hd : Admissible Y Ω K ρ c₀ M Cj floor ε d) (hK : 0 < K)
    (P : PhysicalPrincipalData Y d CF CT) (WF : PhysicalFirstCommutatorPacket P CB CS ε)
    (W : ∀ y ∈ Y,PhysicalPotentialQuarticData P y CG CK) (hCG : 0 ≤ CG) (hCK : 0 ≤ CK)
    {φ : Field} (E : HarmonicTestExpansion Y d.γ d.frame φ) (D : AngularModelData E d.radius)
    (hφ : smoothNear φ (bundle Y d.γ)) :
    IntegrableOn (correctedModelFirstComplexDensity P WF W E D) Y := by
  have hr := modelFirstCorrectedDensity_integrableOn hY hΩ hSub hd hK P WF W hCG hCK
    (E.realHigherSobolevSection (5/2:ℝ) (by norm_num)) (E.contDiff_realHigherSobolevSection _ _)
    E.supportSet E.compactSupportSet E.supportSubset (fun x hx => E.realHigherSobolevSection_zero _ _ (by norm_num) hx)
  have hi := modelFirstCorrectedDensity_integrableOn hY hΩ hSub hd hK P WF W hCG hCK
    (E.imagHigherSobolevSection (5/2:ℝ) (by norm_num)) (E.contDiff_imagHigherSobolevSection _ _)
    E.supportSet E.compactSupportSet E.supportSubset (fun x hx => E.imagHigherSobolevSection_zero _ _ (by norm_num) hx)
  apply (hr.add hi).congr
  filter_upwards [ae_restrict_mem hY.measurableSet] with x hx
  exact (correctedModelFirstComplexDensity_eq hY hSub hd hK P WF W E D hφ hx).symm

end ShrinkingSpheres.ParallelEnergy
