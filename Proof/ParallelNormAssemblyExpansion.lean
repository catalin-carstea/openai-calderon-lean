import Proof.ParallelNormAssembly

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2800000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter MeasureTheory
open scoped ContDiff Topology InnerProductSpace ENNReal
namespace ShrinkingSpheres.ParallelEnergy
open OAI.AnisotropicCalderon.SphereHarmonic

variable {Y Ω : Set X} {m : ℕ} {K ρ c₀ floor ε CF CT CB CS CG CK : ℝ}
  {M : Fin (m+1) → ℝ} {Cj : Fin 9 → ℝ} {d : Data}

def componentNormDifferenceDensity (P : PhysicalPrincipalData Y d CF CT)
    (WF : PhysicalFirstCommutatorPacket P CB CS ε)
    (W : ∀ y ∈ Y,PhysicalPotentialQuarticData P y CG CK)
    (U : X → SphereSobolev (5/2:ℝ)) (T L : X → SphereL2) (y : X) : ℝ :=
  let Z := sphereSobolevZeroEquiv orthogonalSphereHarmonics denseSphereHarmonics
  metricDensity d.γ y*‖(2:ℝ) • Z (T y)+P.truncatedCovariantCoreSection W U y‖^2 -
    metricDensity d.γ y*‖(2:ℝ) • Z (L y)+P.truncatedFormalAdjointCore WF W U y‖^2 -
    4*(metricDensity d.γ y*‖T y‖^2-metricDensity d.γ y*‖L y‖^2)

lemma componentNormDifferenceDensity_expansion (P : PhysicalPrincipalData Y d CF CT)
    (WF : PhysicalFirstCommutatorPacket P CB CS ε)
    (W : ∀ y ∈ Y,PhysicalPotentialQuarticData P y CG CK)
    (U : X → SphereSobolev (5/2:ℝ)) (T L : X → SphereL2) (y : X) :
    componentNormDifferenceDensity P WF W U T L y=
      ∑ i : Fin 9,componentSectorDensity P WF W U T L i y := by
  have hh := weighted_square_expansion (metricDensity d.γ y)
    (fun k => componentForwardOutputs P W U T k y)
    (fun k => componentAdjointOutputs P WF W U L k y)
  simpa only [componentNormDifferenceDensity,componentSectorDensity,componentForwardOutputs,
    componentAdjointOutputs,PhysicalPrincipalData.truncatedCovariantCoreSection,
    PhysicalPrincipalData.truncatedFormalAdjointCore,LinearIsometryEquiv.norm_map] using hh

/-- Exact pointwise actual expansion, including both real and imaginary components. -/
theorem physical_norm_difference_pointwise (P : PhysicalPrincipalData Y d CF CT)
    (WF : PhysicalFirstCommutatorPacket P CB CS ε)
    (W : ∀ y ∈ Y,PhysicalPotentialQuarticData P y CG CK)
    {φ : Field} (E : HarmonicTestExpansion Y d.γ d.frame φ)
    (D : AngularModelData E d.radius) (y : X) :
    componentNormDifferenceDensity P WF W (E.realHigherSobolevSection (5/2:ℝ) (by norm_num))
      D.realComponent.raisingOutput D.realComponent.loweringOutput y +
    componentNormDifferenceDensity P WF W (E.imagHigherSobolevSection (5/2:ℝ) (by norm_num))
      D.imagComponent.raisingOutput D.imagComponent.loweringOutput y =
      ∑ i : Fin 9,sectorComplexDensity P WF W E D i y := by
  rw [componentNormDifferenceDensity_expansion,componentNormDifferenceDensity_expansion,
    ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl (fun i _ => (sectorComplexDensity_eq_components P WF W E D i y).symm)

private lemma modelSquare_integrable {φ : Field}
    (hY : IsOpen Y) (hSub : Y ⊆ Ω)
    (hd : Admissible Y Ω K ρ c₀ M Cj floor ε d) (hK : 0 < K)
    (E : HarmonicTestExpansion Y d.γ d.frame φ)
    (T : X → SphereL2) (hT : ContDiff ℝ ∞ T) (h0T : ∀ y ∉ E.supportSet,T y=0) :
    IntegrableOn (fun y => metricDensity d.γ y*‖T y‖^2) Y := by
  have hg : Elliptic Y K d.γ :=
    ⟨fun a b => (hd.1.1.1 a b).mono hSub,fun y hy => hd.1.1.2 y (hSub hy)⟩
  exact integrableOn_local_weighted_norm_sq_of_memLp hY.measurableSet
    E.compactSupportSet E.supportSubset T
    (hT.continuous.memLp_of_hasCompactSupport (HasCompactSupport.intro E.compactSupportSet h0T))
    (fun y _ hy => h0T y hy) _ (hg.contDiffOn_density hK).continuousOn
    (fun _ _ => Real.sqrt_nonneg _)

/-- Exact integrated expansion. Integrability of all nine actual sectors and
of each of the four original model-plus-core squares is established first. -/
theorem physical_norm_difference_integral (P : PhysicalPrincipalData Y d CF CT)
    (hY : IsOpen Y) (hΩ : IsOpen Ω) (hSub : Y ⊆ Ω)
    (hd : Admissible Y Ω K ρ c₀ M Cj floor ε d) (hK : 0 < K)
    (WF : PhysicalFirstCommutatorPacket P CB CS ε)
    (W : ∀ y ∈ Y,PhysicalPotentialQuarticData P y CG CK) (hCG : 0 ≤ CG) (hCK : 0 ≤ CK)
    {φ : Field} (E : HarmonicTestExpansion Y d.γ d.frame φ) (D : AngularModelData E d.radius) :
    (P.truncatedForwardSquare W E D-P.truncatedAdjointSquare WF W E D)-
      4*physicalAngularModelGap D=
      ∑ i : Fin 9,∫ y in Y,sectorComplexDensity P WF W E D i y := by
  have hS (i) := sectorComplexDensity_integrable P hY hΩ hSub hd hK WF W hCG hCK E D i
  obtain ⟨hFR,hFI,hAR,hAI⟩ := P.truncatedModelSquares_integrable hY hΩ hSub hd hK WF W hCG hCK E D
  have hTR := modelSquare_integrable hY hSub hd hK E _ D.realComponent.contDiff_raisingOutput
    (fun _ hy => D.realComponent.raisingOutput_zero hy)
  have hTI := modelSquare_integrable hY hSub hd hK E _ D.imagComponent.contDiff_raisingOutput
    (fun _ hy => D.imagComponent.raisingOutput_zero hy)
  have hLR := modelSquare_integrable hY hSub hd hK E _ D.realComponent.contDiff_loweringOutput
    (fun _ hy => D.realComponent.loweringOutput_zero hy)
  have hLI := modelSquare_integrable hY hSub hd hK E _ D.imagComponent.contDiff_loweringOutput
    (fun _ hy => D.imagComponent.loweringOutput_zero hy)
  have hCR := (hFR.sub hAR).sub ((hTR.sub hLR).const_mul 4)
  have hCI := (hFI.sub hAI).sub ((hTI.sub hLI).const_mul 4)
  have hR : (∫ y in Y,componentNormDifferenceDensity P WF W
      (E.realHigherSobolevSection (5/2:ℝ) (by norm_num))
      D.realComponent.raisingOutput D.realComponent.loweringOutput y)=
      (∫ y in Y,metricDensity d.γ y*‖(2:ℝ) •
        sphereSobolevZeroEquiv orthogonalSphereHarmonics denseSphereHarmonics (D.realComponent.raisingOutput y)+
        P.truncatedCovariantCoreSection W (E.realHigherSobolevSection (5/2:ℝ) (by norm_num)) y‖^2)-
      (∫ y in Y,metricDensity d.γ y*‖(2:ℝ) •
        sphereSobolevZeroEquiv orthogonalSphereHarmonics denseSphereHarmonics (D.realComponent.loweringOutput y)+
        P.truncatedFormalAdjointCore WF W (E.realHigherSobolevSection (5/2:ℝ) (by norm_num)) y‖^2)-
      4*((∫ y in Y,metricDensity d.γ y*‖D.realComponent.raisingOutput y‖^2)-
        (∫ y in Y,metricDensity d.γ y*‖D.realComponent.loweringOutput y‖^2)) := by
    dsimp only [componentNormDifferenceDensity]
    have hh := integral_sub (hFR.sub hAR) ((hTR.sub hLR).const_mul 4)
    simpa only [Pi.sub_apply,integral_sub hFR hAR,integral_const_mul,integral_sub hTR hLR] using hh
  have hI : (∫ y in Y,componentNormDifferenceDensity P WF W
      (E.imagHigherSobolevSection (5/2:ℝ) (by norm_num))
      D.imagComponent.raisingOutput D.imagComponent.loweringOutput y)=
      (∫ y in Y,metricDensity d.γ y*‖(2:ℝ) •
        sphereSobolevZeroEquiv orthogonalSphereHarmonics denseSphereHarmonics (D.imagComponent.raisingOutput y)+
        P.truncatedCovariantCoreSection W (E.imagHigherSobolevSection (5/2:ℝ) (by norm_num)) y‖^2)-
      (∫ y in Y,metricDensity d.γ y*‖(2:ℝ) •
        sphereSobolevZeroEquiv orthogonalSphereHarmonics denseSphereHarmonics (D.imagComponent.loweringOutput y)+
        P.truncatedFormalAdjointCore WF W (E.imagHigherSobolevSection (5/2:ℝ) (by norm_num)) y‖^2)-
      4*((∫ y in Y,metricDensity d.γ y*‖D.imagComponent.raisingOutput y‖^2)-
        (∫ y in Y,metricDensity d.γ y*‖D.imagComponent.loweringOutput y‖^2)) := by
    dsimp only [componentNormDifferenceDensity]
    have hh := integral_sub (hFI.sub hAI) ((hTI.sub hLI).const_mul 4)
    simpa only [Pi.sub_apply,integral_sub hFI hAI,integral_const_mul,integral_sub hTI hLI] using hh
  calc
    _ = (∫ y in Y,componentNormDifferenceDensity P WF W
        (E.realHigherSobolevSection (5/2:ℝ) (by norm_num))
        D.realComponent.raisingOutput D.realComponent.loweringOutput y)+
      (∫ y in Y,componentNormDifferenceDensity P WF W
        (E.imagHigherSobolevSection (5/2:ℝ) (by norm_num))
        D.imagComponent.raisingOutput D.imagComponent.loweringOutput y) := by
      rw [hR,hI]
      unfold PhysicalPrincipalData.truncatedForwardSquare PhysicalPrincipalData.truncatedAdjointSquare physicalAngularModelGap
      ring
    _ = ∫ y in Y,(componentNormDifferenceDensity P WF W
        (E.realHigherSobolevSection (5/2:ℝ) (by norm_num))
        D.realComponent.raisingOutput D.realComponent.loweringOutput y)+
      (componentNormDifferenceDensity P WF W
        (E.imagHigherSobolevSection (5/2:ℝ) (by norm_num))
        D.imagComponent.raisingOutput D.imagComponent.loweringOutput y) :=
      (integral_add hCR hCI).symm
    _ = ∫ y in Y,∑ i : Fin 9,sectorComplexDensity P WF W E D i y :=
      integral_congr_ae (Eventually.of_forall (physical_norm_difference_pointwise P WF W E D))
    _ = _ := integral_finsetSum Finset.univ (fun i _ => hS i)

end ShrinkingSpheres.ParallelEnergy
