import Proof.ParallelNormAssemblyReservedModelZeroIntegrable

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2800000
set_option maxRecDepth 10000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter MeasureTheory
open scoped ContDiff Topology InnerProductSpace ENNReal
namespace ShrinkingSpheres.ParallelEnergy
open OAI.AnisotropicCalderon.SphereHarmonic

lemma model_potential_corrected_core_integrable {Y Ω : Set X} {m : ℕ}
    {K ρ c₀ floor ε CF CT CG CK : ℝ} {M : Fin (m+1) → ℝ} {Cj : Fin 9 → ℝ} {d : Data}
    (P : PhysicalPrincipalData Y d CF CT) (hY : IsOpen Y) (hSub : Y ⊆ Ω)
    (hd : Admissible Y Ω K ρ c₀ M Cj floor ε d) (hK : 0 < K)
    (hCG : 0 ≤ CG) (hCK : 0 ≤ CK)
    (W : ∀ y ∈ Y,PhysicalPotentialQuarticData P y CG CK)
    (U : X → SphereSobolev (5/2:ℝ)) (hU : ContDiff ℝ ∞ U)
    (S : Set X) (hS : IsCompact S) (hSY : S ⊆ Y) (hU0 : ∀ x ∉ S,U x=0) :
    IntegrableOn (modelPotentialCorrectedCoreDensity P W U) Y := by
  let U2 := fiveHalfToTwoSection U
  let R := modelRaisingSection d U2
  let A := fun x => modelLoweringSection d U2 x-modelAdjointDefectSection d U2 x
  have hg : Elliptic Y K d.γ :=
    ⟨fun a b => (hd.1.1.1 a b).mono hSub,fun x hx => hd.1.1.2 x (hSub hx)⟩
  have he (i : I) : ContDiffOn ℝ ∞ (fun x => d.frame x i) Y := (hd.1.2.2.2.2.2.2.1 i).mono hSub
  have hlog := hd.2.2.2.2.1.1.log (fun x hx => (hd.2.2.2.2.1.2 x hx).1.ne')
  have hU2 : ContDiff ℝ ∞ U2 := (sphereSobolevInclusionL (5/2:ℝ) 2 (by norm_num)).contDiff.comp hU
  have hU20 (x : X) (hx : x ∉ S) : U2 x=0 := by simp only [U2,fiveHalfToTwoSection,hU0 x hx,map_zero]
  have hSmooth := contDiff_supported_modelCovariantSections hY d hg hK he hlog U2 hU2 S hS.isClosed hSY hU20
  have h0 (x : X) (hx : x ∉ S) := modelCovariantSections_zero_off d U2 S hS.isClosed hU20 x hx
  have hR0 (x : X) (hx : x ∉ S) : R x=0 := (h0 x hx).1
  have hA0 (x : X) (hx : x ∉ S) : A x=0 := by simp only [A,(h0 x hx).2.1,(h0 x hx).2.2,sub_self]
  have hRlp : MemLp R 2 (volume.restrict Y) :=
    (hSmooth.1.continuous.memLp_of_hasCompactSupport (HasCompactSupport.intro hS hR0)).restrict _
  have hAlp : MemLp A 2 (volume.restrict Y) :=
    ((hSmooth.2.1.sub hSmooth.2.2).continuous.memLp_of_hasCompactSupport (HasCompactSupport.intro hS hA0)).restrict _
  have hPF := P.potentialQuadraticCoreSection_memLp hY hSub hd hK W hCK U hU S hS hSY hU0 2
  have hPA := P.potentialQuadraticAdjointCoreSection_memLp hY hSub hd hK W hCG hCK U hU S hS hSY hU0 2
  have hIF := integrableOn_local_weighted_inner_of_memLp hY.measurableSet hS hSY R _ hRlp hPF
    (fun x _ hx => hR0 x hx) (metricDensity d.γ) (hg.contDiffOn_density hK).continuousOn
  have hIA := integrableOn_local_weighted_inner_of_memLp hY.measurableSet hS hSY A _ hAlp hPA
    (fun x _ hx => hA0 x hx) (metricDensity d.γ) (hg.contDiffOn_density hK).continuousOn
  have hEq : modelPotentialCorrectedCoreDensity P W U=fun x =>
      4*(metricDensity d.γ x*⟪R x,P.potentialQuadraticCoreSection W U x⟫_ℝ-
        metricDensity d.γ x*⟪A x,P.potentialQuadraticAdjointCoreSection W U x⟫_ℝ) := by
    funext x
    dsimp only [modelPotentialCorrectedCoreDensity,R,A,U2]
    ring
  rw [hEq]
  exact (hIF.sub hIA).const_mul 4

/-- Literal corrected model/potential integrability for arbitrary SAME
packets, proved through actual smooth supported model and potential outputs. -/
theorem corrected_model_potential_sector_integrable {Y Ω : Set X} {m : ℕ}
    {K ρ c₀ floor ε CF CT CB CS CG CK : ℝ} {M : Fin (m+1) → ℝ} {Cj : Fin 9 → ℝ} {d : Data}
    (P : PhysicalPrincipalData Y d CF CT) (hY : IsOpen Y) (hSub : Y ⊆ Ω)
    (hd : Admissible Y Ω K ρ c₀ M Cj floor ε d) (hK : 0 < K)
    (WF : PhysicalFirstCommutatorPacket P CB CS ε) (hCG : 0 ≤ CG) (hCK : 0 ≤ CK)
    (W : ∀ y ∈ Y,PhysicalPotentialQuarticData P y CG CK)
    {φ : Field} (E : HarmonicTestExpansion Y d.γ d.frame φ) (D : AngularModelData E d.radius)
    (hφ : smoothNear φ (bundle Y d.γ)) :
    IntegrableOn (correctedModelSectorComplexDensity P WF W E D 2) Y := by
  obtain ⟨Q,hQ⟩ := exists_unit_boundary_coefficient
  have hr := model_potential_corrected_core_integrable P hY hSub hd hK hCG hCK W
    (E.realHigherSobolevSection (5/2:ℝ) (by norm_num)) (E.contDiff_realHigherSobolevSection _ _)
    E.supportSet E.compactSupportSet E.supportSubset
    (fun x hx => E.realHigherSobolevSection_zero _ _ (by norm_num) hx)
  have hi := model_potential_corrected_core_integrable P hY hSub hd hK hCG hCK W
    (E.imagHigherSobolevSection (5/2:ℝ) (by norm_num)) (E.contDiff_imagHigherSobolevSection _ _)
    E.supportSet E.compactSupportSet E.supportSubset
    (fun x hx => E.imagHigherSobolevSection_zero _ _ (by norm_num) hx)
  apply (hr.add hi).congr
  filter_upwards [ae_restrict_mem hY.measurableSet] with y hy
  have hR := component_corrected_model_potential_eq hY hSub hd hK P WF W Q hQ E Complex.reCLM D.realComponent hφ hy
  have hI := component_corrected_model_potential_eq hY hSub hd hK P WF W Q hQ E Complex.imCLM D.imagComponent hφ hy
  exact (congrArg₂ (fun x y : ℝ => x+y) hR hI).symm

end ShrinkingSpheres.ParallelEnergy
