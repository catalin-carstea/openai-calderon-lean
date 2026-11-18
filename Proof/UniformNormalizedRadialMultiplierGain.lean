import Proof.MidpointRadialMultiplierGain

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter MeasureTheory
open scoped ContDiff Topology ENNReal
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.EnergyBridge OAI.AnisotropicCalderon.DirichletFamily
open OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open OAI.AnisotropicCalderon.SphereHarmonic OAI.AnisotropicCalderon.SpectralCoreRegularity
open OAI.AnisotropicCalderon.NativeThreeHalfCoefficientMultiplier

/-- The gained scalar commutator of one genuine actual radial remainder.
The high first variation and the H1 midpoint both use the same canonical
bounded correction. All equations refer to the same coefficient witnesses. -/
structure RadialMultiplierGainData (F F0 F1 : SmoothCoefficientMatrix 2)
    (ha : MemLp (fun z => TauCeti.PDE.energyIntegrand (coefficientMatrixField 2 F z) 0 0) ⊤
      ((volume:Measure X).restrict ballOpens))
    (ha0 : MemLp (fun z => TauCeti.PDE.energyIntegrand (coefficientMatrixField 2 F0 z) 0 0) ⊤
      ((volume:Measure X).restrict ballOpens))
    (ha1 : MemLp (fun z => TauCeti.PDE.energyIntegrand (coefficientMatrixField 2 F1 z) 0 0) ⊤
      ((volume:Measure X).restrict ballOpens))
    (ell : X →L[ℝ] ℝ) (Qm : SmoothCoefficientJets 3) (r C : ℝ) : Prop where
  norm_bound : ‖radialTaylorMultiplierCommutatorL F F0 F1 ha ha0 ha1 Qm r‖ ≤ C*r^2
  canonical_first_graph : ∀ f : SphereSobolev (3/2:ℝ),
    sphereSobolevInclusionL (1/2:ℝ) 0 (by norm_num)
      (halfMultiplierFirstVariationL F0 F1 ha1 Qm (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num) f)) =
    radialCorrectionCovectorL ell
      (coarseSphereScalarMulL (smoothSphereValue (nativeH2CoefficientSmoothData Qm))
        (sphereSobolevInclusionL (3/2:ℝ) 0 (by norm_num) f))-
    coarseSphereScalarMulL (smoothSphereValue (nativeH2CoefficientSmoothData Qm))
      (radialCorrectionCovectorL ell (sphereSobolevInclusionL (3/2:ℝ) 0 (by norm_num) f))
  midpoint_graph : ∀ R : SphereSobolev 1 →L[ℝ] SphereSobolev 0,
    (sphereSobolevInclusionL (1/2:ℝ) 0 (by norm_num)).comp (actualHighRadialErrorL F) =
      R.comp (sphereSobolevInclusionL (3/2:ℝ) 1 (by norm_num)) →
    (sphereSobolevInclusionL (1/2:ℝ) 0 (by norm_num)).comp
      ((radialTaylorMultiplierCommutatorL F F0 F1 ha ha0 ha1 Qm r).comp
        (sphereSobolevInclusionL 1 (1/2:ℝ) (by norm_num))) =
    (R-r • ((radialCorrectionCovectorL ell).comp (sphereSobolevInclusionL 1 0 (by norm_num)))).comp
      (oneBoundaryCoefficientMulL (smoothMultiplierLowerJets Qm))-
    (coarseSphereScalarMulL (smoothSphereValue (nativeH2CoefficientSmoothData Qm))).comp
      (R-r • ((radialCorrectionCovectorL ell).comp (sphereSobolevInclusionL 1 0 (by norm_num))))

/-- A complete uniform gained scalar commutator for the actual normalized
radial Taylor remainder, including the exact canonical first variation and
all-H1 midpoint graph. No frame derivative bounds or cutoff norms occur. -/
theorem uniform_normalized_radial_multiplier_gain {Y Ω : Set X} (hΩ : IsOpen Ω)
    {m : ℕ} (hm : 3 ≤ m) (K ρ c₀ : ℝ) (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ)
    (hK : 1 ≤ K) (hρ : 0 < ρ) :
    ∃ η CGain : ℝ,∃ F0 : SmoothCoefficientMatrix 2,
    ∃ ha0 : MemLp (fun z => TauCeti.PDE.energyIntegrand (coefficientMatrixField 2 F0 z) 0 0) ⊤
      ((volume:Measure X).restrict ballOpens),
    0 < η ∧ 0 ≤ CGain ∧
    (∀ z ∈ Metric.closedBall (0:X) 2,coefficientMatrixField 2 F0 z = 1) ∧
    ∀ floor,1 ≤ floor → ∀ ε,0 ≤ ε → ε ≤ η → ∀ d,
    Admissible Y Ω K ρ c₀ M Cj floor ε d → ∀ y ∈ Y,
    ∀ F F1 : SmoothCoefficientMatrix 2,
    (∀ z ∈ Metric.closedBall (0:X) 2,∀ i j,coefficientValue 2 (F i j) =ᶠ[𝓝 z]
      (fun w => normalizedFirstNormalCoefficient d y w i j)) →
    (∀ z ∈ Metric.closedBall (0:X) 2,∀ i j,coefficientValue 2 (F1 i j) =ᶠ[𝓝 z]
      (fun w => firstDensityLogCovector d y w*(1:Mat) i j)) →
    ∃ ha : MemLp (fun z => TauCeti.PDE.energyIntegrand (coefficientMatrixField 2 F z) 0 0) ⊤
      ((volume:Measure X).restrict ballOpens),
    ∃ ha1 : MemLp (fun z => TauCeti.PDE.energyIntegrand (coefficientMatrixField 2 F1 z) 0 0) ⊤
      ((volume:Measure X).restrict ballOpens),
    IsCoercive (TauCeti.PDE.energyFormH1L0 ha) ∧
    (strongDirichletOperator fixedSobolevCalculus 0 F).IsInvertible ∧
    (strongDirichletOperator fixedSobolevCalculus 0 F0).IsInvertible ∧
    ∀ Qm : SmoothCoefficientJets 3,∀ B : ℝ,0 ≤ B →
    (∀ j,∀ z ∈ (ballOpens:Set X),|(gradient (coefficientValue 3 Qm) z) j| ≤ B) →
    (∀ j,∀ z ∈ (ballOpens:Set X),‖gradient (fun w => (gradient (coefficientValue 3 Qm) w) j) z‖ ≤ B) →
    RadialMultiplierGainData F F0 F1 ha ha0 ha1 (firstDensityLogCovector d y) Qm (d.radius y) (CGain*B) := by
  obtain ⟨η,CGain,F0,ha0,hη,hCGain,hFlat,hPoint⟩ :=
    uniform_normalized_multiplier_commutator_taylor (Y:=Y) hΩ hm K ρ c₀ M Cj hK hρ
  refine ⟨η,CGain,F0,ha0,hη,hCGain,hFlat,?_⟩
  intro floor hf ε hε hSmall d hd y hy F F1 hRep hRep1
  obtain ⟨ha,ha1,hc,hInv,hInv0,hNorm⟩ := hPoint floor hf ε hε hSmall d hd y hy F F1 hRep hRep1
  have hFlatB (z : X) (hz : z ∈ (ballOpens:Set X)) := hFlat z (unitBall_subset_closedBall_two hz)
  have hc0 := flat_compact_coefficient_energy_coercive F0 ha0 hFlatB
  have hF1 (z : X) (hz : z ∈ (ballOpens:Set X)) (i j : I) :
      coefficientValue 2 (F1 i j) z = firstDensityLogCovector d y z*(1:Mat) i j :=
    (hRep1 z (unitBall_subset_closedBall_two hz) i j).eq_of_nhds
  refine ⟨ha,ha1,hc,hInv,hInv0,?_⟩
  intro Qm B hB hQ1 hQ2
  refine ⟨hNorm Qm B hB hQ1 hQ2,?_,?_⟩
  · intro f
    exact halfMultiplierFirstVariation_canonical_graph F0 F1 ha0 ha1 hc0 hFlatB (firstDensityLogCovector d y) hF1 hInv0 Qm f
  · intro R hHigh
    exact midpoint_radial_taylor_multiplier_gain_graph F F0 F1 ha ha0 ha1 hc hFlatB
      (firstDensityLogCovector d y) hF1 hInv hInv0 R hHigh Qm (d.radius y)

end ShrinkingSpheres
