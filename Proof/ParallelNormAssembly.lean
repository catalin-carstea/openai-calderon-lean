import Proof.ParallelNormAssemblyAlgebra

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2800000
set_option maxRecDepth 10000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
open Set Filter MeasureTheory
open scoped ContDiff Topology InnerProductSpace ENNReal
namespace ShrinkingSpheres.ParallelEnergy
open OAI.AnisotropicCalderon.SphereHarmonic

variable {Y Ω : Set X} {m : ℕ} {K ρ c₀ floor ε CF CT CB CS CG CK : ℝ}
  {M : Fin (m+1) → ℝ} {Cj : Fin 9 → ℝ} {d : Data}

/-- Scalar, complete effective first, quadratic potential, actual model raising.
Every inclusion is the genuine declared inclusion, before taking the fibre norm. -/
def componentForwardOutputs (P : PhysicalPrincipalData Y d CF CT)
    (W : ∀ y ∈ Y,PhysicalPotentialQuarticData P y CG CK)
    (U : X → SphereSobolev (5/2:ℝ)) (T : X → SphereL2) : Fin 4 → X → SphereSobolev 0
  | 0 => scalarCovariantSecondSection d (scalarPrincipalMatrix d.γ d.g₂ d.radius) (fiveHalfToTwoSection U)
  | 1 => P.firstCovariantCoreSection (fiveHalfToTwoSection U)
  | 2 => P.potentialQuadraticCoreSection W U
  | 3 => fun y => sphereSobolevZeroEquiv orthogonalSphereHarmonics denseSphereHarmonics (T y)

/-- The physically weighted adjoints of the SAME three residual operators,
and actual model lowering, with no replacement Hilbert partners. -/
def componentAdjointOutputs (P : PhysicalPrincipalData Y d CF CT)
    (WF : PhysicalFirstCommutatorPacket P CB CS ε)
    (W : ∀ y ∈ Y,PhysicalPotentialQuarticData P y CG CK)
    (U : X → SphereSobolev (5/2:ℝ)) (L : X → SphereL2) : Fin 4 → X → SphereSobolev 0
  | 0 => scalarCovariantSecondTransposeSection d (metricDensity d.γ)
      (scalarPrincipalMatrix d.γ d.g₂ d.radius) (fiveHalfToTwoSection U)
  | 1 => P.firstFormalAdjointCore WF W U
  | 2 => P.potentialQuadraticAdjointCoreSection W U
  | 3 => fun y => sphereSobolevZeroEquiv orthogonalSphereHarmonics denseSphereHarmonics (L y)

def componentSectorDensity (P : PhysicalPrincipalData Y d CF CT)
    (WF : PhysicalFirstCommutatorPacket P CB CS ε)
    (W : ∀ y ∈ Y,PhysicalPotentialQuarticData P y CG CK)
    (U : X → SphereSobolev (5/2:ℝ)) (T L : X → SphereL2) (i : Fin 9) (y : X) : ℝ :=
  weightedSquareSector (metricDensity d.γ y)
    (fun k => componentForwardOutputs P W U T k y)
    (fun k => componentAdjointOutputs P WF W U L k y) i

/-- The nine physical sectors, adding real and imaginary tests. The two
parallel workers' shared densities occur literally at indices 1 and 3. -/
def sectorComplexDensity (P : PhysicalPrincipalData Y d CF CT)
    (WF : PhysicalFirstCommutatorPacket P CB CS ε)
    (W : ∀ y ∈ Y,PhysicalPotentialQuarticData P y CG CK)
    {φ : Field} (E : HarmonicTestExpansion Y d.γ d.frame φ)
    (D : AngularModelData E d.radius) (i : Fin 9) (y : X) : ℝ :=
  match i with
  | 1 => firstSelfComplexDensity P WF W E y
  | 3 => scalarFirstComplexDensity P WF W E y
  | _ => componentSectorDensity P WF W (E.realHigherSobolevSection (5/2:ℝ) (by norm_num))
      D.realComponent.raisingOutput D.realComponent.loweringOutput i y +
    componentSectorDensity P WF W (E.imagHigherSobolevSection (5/2:ℝ) (by norm_num))
      D.imagComponent.raisingOutput D.imagComponent.loweringOutput i y

lemma sectorComplexDensity_eq_components (P : PhysicalPrincipalData Y d CF CT)
    (WF : PhysicalFirstCommutatorPacket P CB CS ε)
    (W : ∀ y ∈ Y,PhysicalPotentialQuarticData P y CG CK)
    {φ : Field} (E : HarmonicTestExpansion Y d.γ d.frame φ)
    (D : AngularModelData E d.radius) (i : Fin 9) (y : X) :
    sectorComplexDensity P WF W E D i y =
    componentSectorDensity P WF W (E.realHigherSobolevSection (5/2:ℝ) (by norm_num))
      D.realComponent.raisingOutput D.realComponent.loweringOutput i y +
    componentSectorDensity P WF W (E.imagHigherSobolevSection (5/2:ℝ) (by norm_num))
      D.imagComponent.raisingOutput D.imagComponent.loweringOutput i y := by
  fin_cases i <;> rfl

lemma componentOutputs_L2 (P : PhysicalPrincipalData Y d CF CT)
    (hY : IsOpen Y) (hΩ : IsOpen Ω) (hSub : Y ⊆ Ω)
    (hd : Admissible Y Ω K ρ c₀ M Cj floor ε d) (hK : 0 < K)
    (WF : PhysicalFirstCommutatorPacket P CB CS ε)
    (W : ∀ y ∈ Y,PhysicalPotentialQuarticData P y CG CK) (hCG : 0 ≤ CG) (hCK : 0 ≤ CK)
    (U : X → SphereSobolev (5/2:ℝ)) (hU : ContDiff ℝ ∞ U)
    (S : Set X) (hS : IsCompact S) (hSY : S ⊆ Y) (h0U : ∀ y ∉ S,U y=0)
    (T L : X → SphereL2) (hT : ContDiff ℝ ∞ T) (hL : ContDiff ℝ ∞ L)
    (h0T : ∀ y ∉ S,T y=0) (h0L : ∀ y ∉ S,L y=0) :
    (∀ k,MemLp (componentForwardOutputs P W U T k) 2 (volume.restrict Y)) ∧
    (∀ k,MemLp (componentAdjointOutputs P WF W U L k) 2 (volume.restrict Y)) ∧
    (∀ k,∀ y ∉ S,componentForwardOutputs P W U T k y=0) ∧
    (∀ k,∀ y ∉ S,componentAdjointOutputs P WF W U L k y=0) := by
  have hU2 : ContDiff ℝ ∞ (fiveHalfToTwoSection U) :=
    (sphereSobolevInclusionL (5/2:ℝ) 2 (by norm_num)).contDiff.comp hU
  have h0U2 (y) (hy : y ∉ S) : fiveHalfToTwoSection U y=0 := by
    simp only [fiveHalfToTwoSection,h0U y hy,map_zero]
  have hw := hd.contDiffOn_scalarPrincipalConnectionWeight hY hSub hK
  have hSc := physical_scalar_principal_core_memLp hY hSub hd hK _ hU2 S hS hSY h0U2 2
  have hSc0 := physical_scalar_principal_core_supported hY hSub hd hK _ hU2 S hS.isClosed hSY h0U2
  have hF := P.firstCovariantCoreSection_memLp hY hΩ hSub hd hK _ hU2 S hS hSY h0U2 hw 2
  have hA := P.firstFormalAdjointCore_memLp hY hΩ hSub hd hK WF W hCG hCK U hU S hS hSY h0U hw 2
  have hV := P.potentialQuadraticCoreSection_memLp hY hSub hd hK W hCK U hU S hS hSY h0U 2
  have hVA := P.potentialQuadraticAdjointCoreSection_memLp hY hSub hd hK W hCG hCK U hU S hS hSY h0U 2
  let Z := sphereSobolevZeroEquiv orthogonalSphereHarmonics denseSphereHarmonics
  have hZT := (Z.contDiff.comp hT).continuous.memLp_of_hasCompactSupport
    (μ := volume.restrict Y) (p := 2)
    (HasCompactSupport.intro hS (fun y hy => by change Z (T y)=0;rw [h0T y hy,map_zero]))
  have hZL := (Z.contDiff.comp hL).continuous.memLp_of_hasCompactSupport
    (μ := volume.restrict Y) (p := 2)
    (HasCompactSupport.intro hS (fun y hy => by change Z (L y)=0;rw [h0L y hy,map_zero]))
  refine ⟨?_,?_,?_,?_⟩
  · intro k
    fin_cases k
    · exact hSc.1
    · exact hF
    · exact hV
    · exact hZT
  · intro k
    fin_cases k
    · exact hSc.2
    · exact hA
    · exact hVA
    · exact hZL
  · intro k y hy
    fin_cases k
    · exact hSc0.1.2 y hy
    · change ∑ b : I,P.firstCovariantCoreRow (fiveHalfToTwoSection U) b y=0
      exact Finset.sum_eq_zero (fun b _ =>
        (P.firstCovariantCoreRow_supported hY hΩ hSub hd hK _ hU2 S hS.isClosed hSY h0U2 b (hw b)).2 y hy)
    · exact P.potentialQuadraticCoreSection_zero_of_source_zero W U (h0U y hy)
    · simp only [componentForwardOutputs,h0T y hy,map_zero]
  · intro k y hy
    fin_cases k
    · exact hSc0.2.2 y hy
    · exact P.firstFormalAdjointCore_zero_off hY hd WF W U hU S hS.isClosed hSY h0U hw hy
    · exact P.potentialQuadraticAdjointCoreSection_zero_of_source_zero W U (h0U y hy)
    · simp only [componentAdjointOutputs,h0L y hy,map_zero]

/-- Qualitative integrability of every signed physical sector. No sector
estimate or smooth choice of higher endpoint witnesses is assumed. -/
theorem sectorComplexDensity_integrable (P : PhysicalPrincipalData Y d CF CT)
    (hY : IsOpen Y) (hΩ : IsOpen Ω) (hSub : Y ⊆ Ω)
    (hd : Admissible Y Ω K ρ c₀ M Cj floor ε d) (hK : 0 < K)
    (WF : PhysicalFirstCommutatorPacket P CB CS ε)
    (W : ∀ y ∈ Y,PhysicalPotentialQuarticData P y CG CK) (hCG : 0 ≤ CG) (hCK : 0 ≤ CK)
    {φ : Field} (E : HarmonicTestExpansion Y d.γ d.frame φ)
    (D : AngularModelData E d.radius) (i : Fin 9) :
    IntegrableOn (sectorComplexDensity P WF W E D i) Y := by
  have hg : Elliptic Y K d.γ :=
    ⟨fun a b => (hd.1.1.1 a b).mono hSub,fun y hy => hd.1.1.2 y (hSub hy)⟩
  have hPer (U : X → SphereSobolev (5/2:ℝ)) (hU : ContDiff ℝ ∞ U)
      (h0U : ∀ y ∉ E.supportSet,U y=0) (T L : X → SphereL2)
      (hT : ContDiff ℝ ∞ T) (hL : ContDiff ℝ ∞ L)
      (h0T : ∀ y ∉ E.supportSet,T y=0) (h0L : ∀ y ∉ E.supportSet,L y=0) :
      IntegrableOn (componentSectorDensity P WF W U T L i) Y := by
    obtain ⟨hF,hA,hzF,hzA⟩ := componentOutputs_L2 P hY hΩ hSub hd hK WF W hCG hCK U hU
      E.supportSet E.compactSupportSet E.supportSubset h0U T L hT hL h0T h0L
    exact weightedSquareSector_integrable hY.measurableSet E.compactSupportSet E.supportSubset
      (metricDensity d.γ) (hg.contDiffOn_density hK).continuousOn (fun _ _ => Real.sqrt_nonneg _)
      _ _ hF hA (fun k y _ hy => hzF k y hy) (fun k y _ hy => hzA k y hy) i
  have hR := hPer (E.realHigherSobolevSection (5/2:ℝ) (by norm_num))
    (E.contDiff_realHigherSobolevSection _ (by norm_num))
    (fun _ hy => E.realHigherSobolevSection_zero _ (by norm_num) (by norm_num) hy)
    _ _ D.realComponent.contDiff_raisingOutput D.realComponent.contDiff_loweringOutput
    (fun _ hy => D.realComponent.raisingOutput_zero hy) (fun _ hy => D.realComponent.loweringOutput_zero hy)
  have hI := hPer (E.imagHigherSobolevSection (5/2:ℝ) (by norm_num))
    (E.contDiff_imagHigherSobolevSection _ (by norm_num))
    (fun _ hy => E.imagHigherSobolevSection_zero _ (by norm_num) (by norm_num) hy)
    _ _ D.imagComponent.contDiff_raisingOutput D.imagComponent.contDiff_loweringOutput
    (fun _ hy => D.imagComponent.raisingOutput_zero hy) (fun _ hy => D.imagComponent.loweringOutput_zero hy)
  exact (hR.add hI).congr (Eventually.of_forall (fun y => (sectorComplexDensity_eq_components P WF W E D i y).symm))

end ShrinkingSpheres.ParallelEnergy
