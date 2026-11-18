import Proof.ParallelNormAssemblyConditional

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

/-- Keep the integrator's five cross sectors together when their estimates
require cancellation across scalar/potential, first/potential and model terms. -/
def reservedComplexDensity (P : PhysicalPrincipalData Y d CF CT)
    (WF : PhysicalFirstCommutatorPacket P CB CS ε)
    (W : ∀ y ∈ Y,PhysicalPotentialQuarticData P y CG CK)
    {φ : Field} (E : HarmonicTestExpansion Y d.γ d.frame φ)
    (D : AngularModelData E d.radius) (y : X) : ℝ :=
  sectorComplexDensity P WF W E D 4 y+sectorComplexDensity P WF W E D 5 y+
    sectorComplexDensity P WF W E D 6 y+sectorComplexDensity P WF W E D 7 y+
    sectorComplexDensity P WF W E D 8 y

/-- The first four sectors and the single complete reserved sum. -/
def compressedComplexDensity (P : PhysicalPrincipalData Y d CF CT)
    (WF : PhysicalFirstCommutatorPacket P CB CS ε)
    (W : ∀ y ∈ Y,PhysicalPotentialQuarticData P y CG CK)
    {φ : Field} (E : HarmonicTestExpansion Y d.γ d.frame φ)
    (D : AngularModelData E d.radius) : Fin 5 → X → ℝ
  | 0 => sectorComplexDensity P WF W E D 0
  | 1 => firstSelfComplexDensity P WF W E
  | 2 => sectorComplexDensity P WF W E D 2
  | 3 => scalarFirstComplexDensity P WF W E
  | 4 => reservedComplexDensity P WF W E D

lemma sum_sectors_eq_compressed (P : PhysicalPrincipalData Y d CF CT)
    (WF : PhysicalFirstCommutatorPacket P CB CS ε)
    (W : ∀ y ∈ Y,PhysicalPotentialQuarticData P y CG CK)
    {φ : Field} (E : HarmonicTestExpansion Y d.γ d.frame φ)
    (D : AngularModelData E d.radius) (y : X) :
    (∑ i : Fin 9,sectorComplexDensity P WF W E D i y)=
      ∑ i : Fin 5,compressedComplexDensity P WF W E D i y := by
  have h1 : sectorComplexDensity P WF W E D 1=firstSelfComplexDensity P WF W E := rfl
  have h3 : sectorComplexDensity P WF W E D 3=scalarFirstComplexDensity P WF W E := rfl
  simp [Fin.sum_univ_succ,compressedComplexDensity,reservedComplexDensity,h1,h3]
  <;> ring

lemma compressedComplexDensity_integrable (P : PhysicalPrincipalData Y d CF CT)
    (hY : IsOpen Y) (hΩ : IsOpen Ω) (hSub : Y ⊆ Ω)
    (hd : Admissible Y Ω K ρ c₀ M Cj floor ε d) (hK : 0 < K)
    (WF : PhysicalFirstCommutatorPacket P CB CS ε)
    (W : ∀ y ∈ Y,PhysicalPotentialQuarticData P y CG CK) (hCG : 0 ≤ CG) (hCK : 0 ≤ CK)
    {φ : Field} (E : HarmonicTestExpansion Y d.γ d.frame φ)
    (D : AngularModelData E d.radius) (i : Fin 5) :
    IntegrableOn (compressedComplexDensity P WF W E D i) Y := by
  have h (k) := sectorComplexDensity_integrable P hY hΩ hSub hd hK WF W hCG hCK E D k
  fin_cases i
  · exact h 0
  · exact h 1
  · exact h 2
  · exact h 3
  · exact (((((h 4).add (h 5)).add (h 6)).add (h 7)).add (h 8)).congr
      (Eventually.of_forall (fun y => rfl))

/-- The exact integrated expansion also supports a single bound for the
complete reserved sum; it does not demand separately small cross sectors. -/
theorem physical_norm_difference_integral_compressed (P : PhysicalPrincipalData Y d CF CT)
    (hY : IsOpen Y) (hΩ : IsOpen Ω) (hSub : Y ⊆ Ω)
    (hd : Admissible Y Ω K ρ c₀ M Cj floor ε d) (hK : 0 < K)
    (WF : PhysicalFirstCommutatorPacket P CB CS ε)
    (W : ∀ y ∈ Y,PhysicalPotentialQuarticData P y CG CK) (hCG : 0 ≤ CG) (hCK : 0 ≤ CK)
    {φ : Field} (E : HarmonicTestExpansion Y d.γ d.frame φ) (D : AngularModelData E d.radius) :
    (P.truncatedForwardSquare W E D-P.truncatedAdjointSquare WF W E D)-
      4*physicalAngularModelGap D=
      ∑ i : Fin 5,∫ y in Y,compressedComplexDensity P WF W E D i y := by
  rw [physical_norm_difference_integral P hY hΩ hSub hd hK WF W hCG hCK E D]
  rw [← integral_finsetSum Finset.univ (fun i _ =>
    sectorComplexDensity_integrable P hY hΩ hSub hd hK WF W hCG hCK E D i)]
  rw [← integral_finsetSum Finset.univ (fun i _ =>
    compressedComplexDensity_integrable P hY hΩ hSub hd hK WF W hCG hCK E D i)]
  exact integral_congr_ae (Eventually.of_forall (sum_sectors_eq_compressed P WF W E D))

theorem assemble_physical_truncated_norm_comparison_grouped (P : PhysicalPrincipalData Y d CF CT)
    (hY : IsOpen Y) (hΩ : IsOpen Ω) (hSub : Y ⊆ Ω)
    (hd : Admissible Y Ω K ρ c₀ M Cj floor ε d) (hK : 0 < K)
    (WF : PhysicalFirstCommutatorPacket P CB CS ε)
    (W : ∀ y ∈ Y,PhysicalPotentialQuarticData P y CG CK) (hCG : 0 ≤ CG) (hCK : 0 ≤ CK)
    {φ : Field} (E : HarmonicTestExpansion Y d.γ d.frame φ) (D : AngularModelData E d.radius)
    (C : Fin 5 → ℝ)
    (hSector : ∀ i,|∫ y in Y,compressedComplexDensity P WF W E D i y| ≤
      C i*ε*energySq Y d.γ d.frame d.radius φ) :
    |(P.truncatedForwardSquare W E D-P.truncatedAdjointSquare WF W E D)-
      4*physicalAngularModelGap D| ≤ (∑ i : Fin 5,C i)*ε*(energyNorm Y d φ)^2 := by
  rw [physical_norm_difference_integral_compressed P hY hΩ hSub hd hK WF W hCG hCK E D,energyNorm_sq]
  calc
    _ ≤ ∑ i : Fin 5,|∫ y in Y,compressedComplexDensity P WF W E D i y| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i : Fin 5,C i*ε*energySq Y d.γ d.frame d.radius φ :=
      Finset.sum_le_sum (fun i _ => hSector i)
    _ = _ := by rw [Finset.sum_mul,Finset.sum_mul]

/-- Alternative compatibility obligation allowing all five reserved sectors
to cancel with one another. The missing estimates remain explicit. -/
def RemainingGroupedSectorBounds (P : PhysicalPrincipalData Y d CF CT)
    (WF : PhysicalFirstCommutatorPacket P CB CS ε)
    (W : ∀ y ∈ Y,PhysicalPotentialQuarticData P y CG CK) (C : Fin 5 → ℝ) : Prop :=
  ∀ φ,Test Y d.γ d.frame φ →
  ∀ (E : HarmonicTestExpansion Y d.γ d.frame φ) (D : AngularModelData E d.radius),
    |∫ y in Y,firstSelfComplexDensity P WF W E y| ≤ C 1*ε*energySq Y d.γ d.frame d.radius φ ∧
    |∫ y in Y,scalarFirstComplexDensity P WF W E y| ≤ C 3*ε*energySq Y d.γ d.frame d.radius φ ∧
    |∫ y in Y,reservedComplexDensity P WF W E D y| ≤ C 4*ε*energySq Y d.γ d.frame d.radius φ

/-- Uniform conditional caller retaining all reserved cancellations. The
same potential packet, first packet, calculus and remaining estimates must
be selected jointly before tests; this compatibility is an explicit premise. -/
theorem uniform_physical_truncated_norm_comparison_of_grouped_sectors
    (hY : IsOpen Y) (hΩ : IsOpen Ω) (hSub : Y ⊆ Ω) (hm : 3 ≤ m)
    (hK : 1 ≤ K) (Q : SmoothCoefficientJets 2) (B η CB CS CG CK : ℝ) (C : Fin 5 → ℝ)
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
      RemainingGroupedSectorBounds P WF W C) :
    UniformPhysicalTruncatedNormComparison Y Ω K ρ c₀ M Cj CF CT := by
  obtain ⟨C0,hC0,hScalar⟩ := uniform_physical_scalar_self_norm_comparison hY hΩ hSub hm K ρ c₀ M Cj hK
  let c : Fin 5 → ℝ := fun i => if i=0 then C0 else C i
  have hc (i) : 0 ≤ c i := by
    dsimp only [c]
    split_ifs
    · exact hC0
    · exact hC i
  refine ⟨Q,max 1 B,η,∑ i : Fin 5,c i,CB,CS,CG,CK,hQ,hη,
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
  apply assemble_physical_truncated_norm_comparison_grouped P hY hΩ hSub hd (zero_lt_one.trans_le hK)
    WF W hCG hCK E D c
  intro i
  fin_cases i
  · simpa [c,compressedComplexDensity] using h0
  · simpa [c,compressedComplexDensity] using h1
  · simpa [c,compressedComplexDensity] using h2
  · simpa [c,compressedComplexDensity] using h3
  · simpa [c,compressedComplexDensity] using hReserved

end ShrinkingSpheres.ParallelEnergy
