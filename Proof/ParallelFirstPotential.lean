import Proof.ParallelFirstPotentialIntegralAssembly
import Proof.ParallelFirstPotentialBoundedIntegral
import Proof.ParallelFirstPotentialCubicIntegral
import Proof.ParallelFirstPotentialDefect
import Proof.ParallelFirstSelfLeadingBudgets

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

/-- COMPLETE literal effective-first / actual quadratic-potential raw
sector5 estimate. Constants precede all profiles, frames, fixed coherent
WF/W and tests. Both real and imaginary parts and the literal factor2
are retained in the original frozen physical energy. -/
theorem uniform_first_potential_cross_integral_bound
    {Y Ω : Set X} (hY : IsOpen Y) (hΩ : IsOpen Ω) (hSub : Y ⊆ Ω)
    {m : ℕ} (hm : 10 ≤ m) (K ρ c₀ : ℝ) (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ)
    (hK : 1 ≤ K) (hρ : 0 < ρ) (CF CT : ℝ) :
    UniformPotentialSectorEstimate Y Ω K ρ c₀ M Cj CF CT 5 := by
  intro CB CS CG CK hCB _hCS hCG hCK
  obtain ⟨ηP,CP,hηP,hηP1,hCP,hPaired⟩ := uniform_first_potential_paired_integral_bound
    hY hΩ hSub hm K ρ c₀ M Cj hK hρ CF
  obtain ⟨ηD,CD,hηD,hηD1,hCD,hDefect⟩ := uniform_first_potential_defect_integral_bound
    hY hΩ hSub hm K ρ c₀ M Cj hK hρ CF CB CG CK hCB hCG hCK
  obtain ⟨CBound,hCBound,hBounded⟩ := uniform_first_potential_bounded_integral_bound
    hY hΩ hSub hm K ρ c₀ M Cj hK CF CG CK hCG hCK
  obtain ⟨R⟩ := first_self_leading_forward_budget hY hΩ hSub hm K ρ c₀ M Cj hK hρ
  let BW := principalModelDegreeCoordinateBudget K (M ⟨1,by omega⟩) (Cj 2)+6+
    3*principalFirstErrorCoordinateTwoJetBudget K |M ⟨1,by omega⟩| |M ⟨2,by omega⟩| (Cj 2)
  let G := max (physicalPotentialGeneratorBudget CF) CG
  let CQ := 49*potentialWordEntryBudget K
  let CCubic := 6*BW*(6*K*G*CK*CQ)*(3*K^2+1)
  have hG : 0 ≤ G := hCG.trans (le_max_right _ _)
  have hCQ : 0 ≤ CQ := by dsimp only [CQ,potentialWordEntryBudget];positivity
  have hBW : 0 ≤ BW := by
    have hD := principalModelDegreeCoordinateBudget_nonneg K (M ⟨1,by omega⟩) (Cj 2) (zero_le_one.trans hK)
    have hE := principalFirstErrorCoordinateTwoJetBudget_nonneg K |M ⟨1,by omega⟩| |M ⟨2,by omega⟩| (Cj 2)
      (zero_le_one.trans hK) (abs_nonneg _) (abs_nonneg _)
    dsimp only [BW]
    positivity
  have hCCubic : 0 ≤ CCubic := by dsimp only [CCubic];positivity
  let η := min ηP (min ηD R.eta)
  let C := CP+CBound+CCubic+CD
  have hη : 0 < η := lt_min hηP (lt_min hηD R.eta_pos)
  have hη1 : η ≤ 1 := (min_le_left _ _).trans hηP1
  refine ⟨1,η,C,hη,hη1,by dsimp only [C];positivity,?_⟩
  intro floor hf ε hε hSmall d hd P WF W φ hφ E D
  have hε1 := hSmall.trans hη1
  have hSmallP : ε ≤ ηP := hSmall.trans (min_le_left _ _)
  have hSmallD : ε ≤ ηD := hSmall.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hSmallR : ε ≤ R.eta := hSmall.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hRaw := R.raw floor hf ε hε hSmallR d hd CF CT P
  have hP := hPaired floor hf ε hε hSmallP d hd CT CG CK P W φ E D hφ
  have hB := hBounded floor hf ε hε hε1 d hd CT P W φ E D hφ
  have hD := hDefect floor hf ε hε hSmallD d hd CT CS P WF W φ E D hφ
  have hF := firstPotentialComplexDensity_integrable P hY hΩ hSub hd (zero_lt_one.trans_le hK) WF W hCG hCK E D
  have hSplit : ∀ᵐ y ∂volume.restrict Y,firstPotentialComplexDensity P WF W E y=
      firstPotentialPairedComplexDensity P E y+firstPotentialBoundedComplexDensity P W E y-
        firstPotentialCubicComplexDensity P W E y-firstPotentialDefectComplexDensity P WF W E y := by
    filter_upwards [ae_restrict_mem hY.measurableSet] with y hy
    exact firstPotentialComplexDensity_exact_split hY hd P WF W E hy (hRaw y hy)
  have hCN (hInt : IntegrableOn (firstPotentialCubicComplexDensity P W E) Y) :
      |∫ y in Y,firstPotentialCubicComplexDensity P W E y| ≤ CCubic*ε^2*energySq Y d.γ d.frame d.radius φ :=
    firstPotential_cubic_complex_integral_bound hY hSub (by omega) K ρ c₀ M Cj hK CF CG CK hCG hCK
      floor ε hf hε hε1 d hd CT P W φ E D hφ hInt
  have hFinal := firstPotential_integral_assembly (volume.restrict Y)
    (firstPotentialComplexDensity P WF W E) (firstPotentialPairedComplexDensity P E)
    (firstPotentialBoundedComplexDensity P W E) (firstPotentialCubicComplexDensity P W E)
    (firstPotentialDefectComplexDensity P WF W E) hCP hCBound hCCubic hCD hε hε1
    (energySq_nonneg Y d.γ d.frame d.radius φ) hF hP.1 hB.1 hD.1 hSplit hP.2 hB.2 hD.2 hCN
  have hEq : sectorComplexDensity P WF W E D 5=firstPotentialComplexDensity P WF W E :=
    funext (sector_five_eq_firstPotentialComplexDensity P WF W E D)
  rw [hEq]
  exact ⟨hF,hFinal.2⟩

end ShrinkingSpheres.ParallelEnergy
