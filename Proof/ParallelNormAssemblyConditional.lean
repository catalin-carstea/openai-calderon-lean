import Proof.ParallelNormAssemblyExpansion

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
open OAI.AnisotropicCalderon.SphereHarmonic OAI.AnisotropicCalderon.DirichletFamily

variable {Y Ω : Set X} {m : ℕ} {K ρ c₀ floor ε CF CT CB CS CG CK : ℝ}
  {M : Fin (m+1) → ℝ} {Cj : Fin 9 → ℝ} {d : Data}

/-- Genuine higher-to-two inclusions identify the scalar sector with the
already checked physical scalar self-comparison density. -/
lemma scalar_sector_eq (P : PhysicalPrincipalData Y d CF CT)
    (WF : PhysicalFirstCommutatorPacket P CB CS ε)
    (W : ∀ y ∈ Y,PhysicalPotentialQuarticData P y CG CK)
    {φ : Field} (E : HarmonicTestExpansion Y d.γ d.frame φ)
    (D : AngularModelData E d.radius) (y : X) :
    sectorComplexDensity P WF W E D 0 y=
      scalarPrincipalSquareDensity d E y-scalarPrincipalTransposeSquareDensity d E y := by
  have hR : fiveHalfToTwoSection (E.realHigherSobolevSection (5/2:ℝ) (by norm_num))=
      E.realSobolevSection 2 (by norm_num) :=
    funext (E.realHigherSobolevSection_inclusion (5/2:ℝ) 2 (by norm_num) (by norm_num) (by norm_num))
  have hI : fiveHalfToTwoSection (E.imagHigherSobolevSection (5/2:ℝ) (by norm_num))=
      E.imagSobolevSection 2 (by norm_num) :=
    funext (E.imagHigherSobolevSection_inclusion (5/2:ℝ) 2 (by norm_num) (by norm_num) (by norm_num))
  rw [sectorComplexDensity_eq_components]
  simp only [componentSectorDensity,weightedSquareSector,componentForwardOutputs,componentAdjointOutputs,hR,hI,
    scalarPrincipalSquareDensity,scalarPrincipalTransposeSquareDensity]
  ring

lemma potential_sector_eq (P : PhysicalPrincipalData Y d CF CT)
    (WF : PhysicalFirstCommutatorPacket P CB CS ε)
    (W : ∀ y ∈ Y,PhysicalPotentialQuarticData P y CG CK)
    {φ : Field} (E : HarmonicTestExpansion Y d.γ d.frame φ)
    (D : AngularModelData E d.radius) (y : X) :
    sectorComplexDensity P WF W E D 2 y=
      P.potentialForwardSquareDensityFamily E W y-P.potentialAdjointSquareDensityFamily E W y := by
  rw [sectorComplexDensity_eq_components]
  simp only [componentSectorDensity,weightedSquareSector,componentForwardOutputs,componentAdjointOutputs,
    PhysicalPrincipalData.potentialForwardSquareDensityFamily,PhysicalPrincipalData.potentialAdjointSquareDensityFamily]
  ring

lemma scalar_sector_integral_eq (P : PhysicalPrincipalData Y d CF CT)
    (WF : PhysicalFirstCommutatorPacket P CB CS ε)
    (W : ∀ y ∈ Y,PhysicalPotentialQuarticData P y CG CK)
    {φ : Field} (E : HarmonicTestExpansion Y d.γ d.frame φ) (D : AngularModelData E d.radius)
    (hF : IntegrableOn (scalarPrincipalSquareDensity d E) Y)
    (hA : IntegrableOn (scalarPrincipalTransposeSquareDensity d E) Y) :
    (∫ y in Y,sectorComplexDensity P WF W E D 0 y)=
      (∫ y in Y,scalarPrincipalSquareDensity d E y)-
        (∫ y in Y,scalarPrincipalTransposeSquareDensity d E y) := by
  calc
    _ = ∫ y in Y,scalarPrincipalSquareDensity d E y-scalarPrincipalTransposeSquareDensity d E y :=
      integral_congr_ae (Eventually.of_forall (scalar_sector_eq P WF W E D))
    _ = _ := integral_sub hF hA

lemma potential_sector_integral_eq (P : PhysicalPrincipalData Y d CF CT)
    (WF : PhysicalFirstCommutatorPacket P CB CS ε)
    (W : ∀ y ∈ Y,PhysicalPotentialQuarticData P y CG CK)
    {φ : Field} (E : HarmonicTestExpansion Y d.γ d.frame φ) (D : AngularModelData E d.radius)
    (hF : IntegrableOn (P.potentialForwardSquareDensityFamily E W) Y)
    (hA : IntegrableOn (P.potentialAdjointSquareDensityFamily E W) Y) :
    (∫ y in Y,sectorComplexDensity P WF W E D 2 y)=
      (∫ y in Y,P.potentialForwardSquareDensityFamily E W y)-
        (∫ y in Y,P.potentialAdjointSquareDensityFamily E W y) := by
  calc
    _ = ∫ y in Y,P.potentialForwardSquareDensityFamily E W y-P.potentialAdjointSquareDensityFamily E W y :=
      integral_congr_ae (Eventually.of_forall (potential_sector_eq P WF W E D))
    _ = _ := integral_sub hF hA

/-- Conditional finite-sector assembly for the exact physical comparison.
The estimates are for the same P/WF/W, measure, real/imaginary tests and
frozen energy. Every unproved quantitative sector is an explicit premise. -/
theorem assemble_physical_truncated_norm_comparison (P : PhysicalPrincipalData Y d CF CT)
    (hY : IsOpen Y) (hΩ : IsOpen Ω) (hSub : Y ⊆ Ω)
    (hd : Admissible Y Ω K ρ c₀ M Cj floor ε d) (hK : 0 < K)
    (WF : PhysicalFirstCommutatorPacket P CB CS ε)
    (W : ∀ y ∈ Y,PhysicalPotentialQuarticData P y CG CK) (hCG : 0 ≤ CG) (hCK : 0 ≤ CK)
    {φ : Field} (E : HarmonicTestExpansion Y d.γ d.frame φ) (D : AngularModelData E d.radius)
    (C : Fin 9 → ℝ)
    (hSector : ∀ i,|∫ y in Y,sectorComplexDensity P WF W E D i y| ≤
      C i*ε*energySq Y d.γ d.frame d.radius φ) :
    |(P.truncatedForwardSquare W E D-P.truncatedAdjointSquare WF W E D)-
      4*physicalAngularModelGap D| ≤ (∑ i : Fin 9,C i)*ε*(energyNorm Y d φ)^2 := by
  rw [physical_norm_difference_integral P hY hΩ hSub hd hK WF W hCG hCK E D,energyNorm_sq]
  calc
    _ ≤ ∑ i : Fin 9,|∫ y in Y,sectorComplexDensity P WF W E D i y| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i : Fin 9,C i*ε*energySq Y d.γ d.frame d.radius φ :=
      Finset.sum_le_sum (fun i _ => hSector i)
    _ = _ := by rw [Finset.sum_mul,Finset.sum_mul]

lemma weaken_epsilon_square {C ε E a : ℝ} (hC : 0 ≤ C) (hε : 0 ≤ ε) (hε1 : ε ≤ 1)
    (hE : 0 ≤ E) (h : |a| ≤ C*ε^2*E) : |a| ≤ C*ε*E := by
  have hPow : ε^2 ≤ ε := by
    simpa only [pow_two,mul_one] using mul_le_mul_of_nonneg_left hε1 hε
  exact h.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hPow hC) hE)

/-- Explicit compatibility obligation for unfinished sectors. Indices 1 and
3 use the workers' literal shared densities and their exact epsilon bounds.
The five integrator sectors retain both orientations and all factors. -/
def RemainingSectorBounds (P : PhysicalPrincipalData Y d CF CT)
    (WF : PhysicalFirstCommutatorPacket P CB CS ε)
    (W : ∀ y ∈ Y,PhysicalPotentialQuarticData P y CG CK) (C : Fin 9 → ℝ) : Prop :=
  ∀ φ,Test Y d.γ d.frame φ →
  ∀ (E : HarmonicTestExpansion Y d.γ d.frame φ) (D : AngularModelData E d.radius),
    |∫ y in Y,firstSelfComplexDensity P WF W E y| ≤ C 1*ε*energySq Y d.γ d.frame d.radius φ ∧
    |∫ y in Y,scalarFirstComplexDensity P WF W E y| ≤ C 3*ε*energySq Y d.γ d.frame d.radius φ ∧
    (∀ i : Fin 9,4 ≤ i.val → |∫ y in Y,sectorComplexDensity P WF W E D i y| ≤
      C i*ε*energySq Y d.γ d.frame d.radius φ)

/-- Uniform caller with constants before arbitrary profiles/frames, and a
coherent common packet selected before tests. Scalar self is supplied by its
checked theorem. The potential comparison in hProduce is exactly the output
of uniform_physical_truncated_core_calculus; keeping it with the remaining
bounds explicitly records the still-required packet-selection compatibility. -/
theorem uniform_physical_truncated_norm_comparison_of_compatible_sectors
    (hY : IsOpen Y) (hΩ : IsOpen Ω) (hSub : Y ⊆ Ω) (hm : 3 ≤ m)
    (hK : 1 ≤ K) (Q : SmoothCoefficientJets 2) (B η CB CS CG CK : ℝ) (C : Fin 9 → ℝ)
    (hQ : ∀ z ∈ Metric.closedBall (0:X) 1,coefficientValue 2 Q =ᶠ[𝓝 z] (fun _ => (1:ℝ)))
    (hη : 0 < η) (hη1 : η ≤ 1) (hC : ∀ i,0 ≤ C i) (hCG : 0 ≤ CG) (hCK : 0 ≤ CK)
    (hProduce : ∀ floor,B ≤ floor → ∀ ε,0 ≤ ε → ε ≤ η → ∀ d,
      Admissible Y Ω K ρ c₀ M Cj floor ε d → ∀ P : PhysicalPrincipalData Y d CF CT,
      ∃ WF : PhysicalFirstCommutatorPacket P CB CS ε,
      ∃ W : ∀ y ∈ Y,PhysicalPotentialQuarticData P y CG CK,
      PhysicalTruncatedCoreCalculus P WF W ∧
      (∀ φ,∀ E : HarmonicTestExpansion Y d.γ d.frame φ,Test Y d.γ d.frame φ →
        IntegrableOn (P.potentialForwardSquareDensityFamily E W) Y ∧
        IntegrableOn (P.potentialAdjointSquareDensityFamily E W) Y ∧
        |(∫ y in Y,P.potentialForwardSquareDensityFamily E W y)-
          (∫ y in Y,P.potentialAdjointSquareDensityFamily E W y)| ≤ C 2*ε*energySq Y d.γ d.frame d.radius φ) ∧
      RemainingSectorBounds P WF W C) :
    UniformPhysicalTruncatedNormComparison Y Ω K ρ c₀ M Cj CF CT := by
  obtain ⟨C0,hC0,hScalar⟩ := uniform_physical_scalar_self_norm_comparison hY hΩ hSub hm K ρ c₀ M Cj hK
  let c : Fin 9 → ℝ := fun i => if i=0 then C0 else C i
  have hc (i) : 0 ≤ c i := by
    dsimp only [c]
    split_ifs
    · exact hC0
    · exact hC i
  refine ⟨Q,max 1 B,η,∑ i : Fin 9,c i,CB,CS,CG,CK,hQ,hη,
    Finset.sum_nonneg (fun i _ => hc i),hCG,hCK,?_⟩
  intro floor hf ε hε hSmall d hd P
  have hf1 := (le_max_left 1 B).trans hf
  have hfB := (le_max_right 1 B).trans hf
  have hε1 := hSmall.trans hη1
  obtain ⟨WF,W,hCalc,hPot,hRemaining⟩ := hProduce floor hfB ε hε hSmall d hd P
  refine ⟨WF,W,hCalc,?_⟩
  intro φ hφ E D
  obtain ⟨hSF,hSA,hSB⟩ := hScalar floor hf1 ε hε hε1 d hd φ E D hφ
  obtain ⟨hPF,hPA,hPB⟩ := hPot φ E hφ
  obtain ⟨hFirst,hCross,hReserved⟩ := hRemaining φ hφ E D
  have hEN := energySq_nonneg Y d.γ d.frame d.radius φ
  have h0 : |∫ y in Y,sectorComplexDensity P WF W E D 0 y| ≤ C0*ε*energySq Y d.γ d.frame d.radius φ := by
    rw [scalar_sector_integral_eq P WF W E D hSF hSA]
    exact weaken_epsilon_square hC0 hε hε1 hEN hSB
  have h2 : |∫ y in Y,sectorComplexDensity P WF W E D 2 y| ≤ C 2*ε*energySq Y d.γ d.frame d.radius φ := by
    rw [potential_sector_integral_eq P WF W E D hPF hPA]
    exact hPB
  have h1 := hFirst
  have h3 := hCross
  apply assemble_physical_truncated_norm_comparison P hY hΩ hSub hd (zero_lt_one.trans_le hK)
    WF W hCG hCK E D c
  intro i
  fin_cases i
  · simpa [c] using h0
  · simpa [c,sectorComplexDensity] using h1
  · simpa [c] using h2
  · simpa [c,sectorComplexDensity] using h3
  · simpa [c] using hReserved 4 (by decide)
  · simpa [c] using hReserved 5 (by decide)
  · simpa [c] using hReserved 6 (by decide)
  · simpa [c] using hReserved 7 (by decide)
  · simpa [c] using hReserved 8 (by decide)

end ShrinkingSpheres.ParallelEnergy
