import Proof.ParallelNormAssemblyReservedAdjointNormalizedError
import Proof.ParallelNormAssemblyReservedAdjointRaisingJets
import Proof.DegreeAdjointHigherEndpoint

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2800000
set_option maxRecDepth 10000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter
open scoped ContDiff Topology
namespace ShrinkingSpheres.ParallelEnergy
open OAI.AnisotropicCalderon.SphereHarmonic

structure NormalizedGeneratorAdjointFirstJets {Y : Set X} {d : Data} {CF CT : ℝ}
    (P : PhysicalPrincipalData Y d CF CT) (C0 C1 : ℝ) where
  high : PhysicalPotentialGeneratorIndex → X → SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ)
  smooth : ∀ a,ContDiffOn ℝ ∞ (high a) Y
  balanced : ∀ a y,y ∈ Y →
    (sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)).comp (high a y)=
      (normalizedPotentialGeneratorLow P y a).adjoint.comp
        (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num))
  norm_bound : ∀ a y,y ∈ Y → ‖high a y‖ ≤ C0
  jet : ∀ a y,y ∈ Y → ∀ i : I,
    ∃ N : SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ),
      higherOperatorCovariantDerivativeL d (high a) y (axis i)=
        (sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)).comp
          (N.comp (sphereSobolevInclusionL (5/2:ℝ) (3/2:ℝ) (by norm_num))) ∧
      ‖N‖ ≤ C1*beta d.γ d.radius y

/-- All seven normalized generators retain their genuine true-adjoint
HIGH family and FIRST HIGH covariant jet, chosen before W and tests. -/
theorem uniform_normalized_generator_adjoint_first_jets {Y Ω : Set X}
    (hY : IsOpen Y) (hΩ : IsOpen Ω) (hSub : Y ⊆ Ω)
    {m : ℕ} (hm : 10 ≤ m) (K ρ c₀ : ℝ) (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ)
    (hK : 1 ≤ K) (hρ : 0 < ρ) :
    ∃ η C0 C1 : ℝ,0 < η ∧ η ≤ 1 ∧ 0 ≤ C0 ∧ 0 ≤ C1 ∧
    ∀ floor,1 ≤ floor → ∀ ε,0 ≤ ε → ε ≤ η → ∀ d,
    Admissible Y Ω K ρ c₀ M Cj floor ε d → ∀ CF CT : ℝ,∀ P : PhysicalPrincipalData Y d CF CT,
    Nonempty (NormalizedGeneratorAdjointFirstJets P C0 C1) := by
  obtain ⟨ηR,CR0,CR1,hηR,hηR1,hCR0,hCR1,hRaise⟩ := uniform_raising_adjoint_higher_first_jets
    hY hΩ hSub hm K ρ c₀ M Cj hK hρ
  obtain ⟨ηE,CE0,CE1,hηE,hηE1,hCE0,hCE1,hError⟩ := uniform_normalized_coordinate_error_adjoint_first_jets
    hY hΩ hSub hm K ρ c₀ M Cj hK hρ
  let C0 := 2+CR0+CE0
  let C1 := CR1+CE1
  have hC1 : 0 ≤ C1 := add_nonneg hCR1 hCE1
  refine ⟨min ηR ηE,C0,C1,lt_min hηR hηE,(min_le_left _ _).trans hηR1,by dsimp only [C0];positivity,hC1,?_⟩
  intro floor hf ε hε hSmall d hd CF CT P
  obtain ⟨R⟩ := hRaise floor hf ε hε (hSmall.trans (min_le_left _ _)) d hd CF CT P
  obtain ⟨E⟩ := hError floor hf ε hε (hSmall.trans (min_le_right _ _)) d hd CF CT P
  let H : PhysicalPotentialGeneratorIndex → X → SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ) := fun a => match a with
    | .inl _ => fun _ => degreeHigherL
    | .inr (.inl a) => R.high a
    | .inr (.inr a) => E.high a
  have hSmooth (a : PhysicalPotentialGeneratorIndex) : ContDiffOn ℝ ∞ (H a) Y := by
    rcases a with u | (a | a)
    · exact contDiffOn_const
    · exact R.smooth a
    · exact E.smooth a
  have hBalanced (a : PhysicalPotentialGeneratorIndex) (y : X) (hy : y ∈ Y) :
      (sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)).comp (H a y)=
        (normalizedPotentialGeneratorLow P y a).adjoint.comp
          (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)) := by
    rcases a with u | (a | a)
    · simpa only [H,normalizedPotentialGeneratorLow,potentialGeneratorWeight,potentialCoordinateGeneratorLow,
        inv_one,one_smul,degreeHalfL] using degreeHigherL_adjoint_pair
    · simpa only [H,normalizedPotentialGeneratorLow,potentialGeneratorWeight,potentialCoordinateGeneratorLow,
        inv_one,one_smul] using R.balanced a y hy
    · exact E.balanced a y hy
  have hNorm (a : PhysicalPotentialGeneratorIndex) (y : X) (hy : y ∈ Y) : ‖H a y‖ ≤ C0 := by
    rcases a with u | (a | a)
    · exact norm_degreeHigherL_le_two.trans (by dsimp only [C0];linarith only [hCR0,hCE0])
    · exact (R.norm_bound a y hy).trans (by dsimp only [C0];linarith only [hCE0])
    · exact (E.norm_bound a y hy).trans (by dsimp only [C0];linarith only [hCR0])
  refine ⟨{ high := H,smooth := hSmooth,balanced := hBalanced,norm_bound := hNorm,jet := ?_ }⟩
  intro a y hy i
  rcases a with u | (a | a)
  · refine ⟨0,?_,by rw [norm_zero];exact mul_nonneg hC1 (Real.sqrt_nonneg _)⟩
    have hh := higher_covariant_derivative_eq_half d (fun _ => degreeHalfL) (fun _ => degreeHigherL) y (axis i)
      contDiffAt_const contDiffAt_const (Eventually.of_forall (fun _ => degreeHalf_balanced))
    rw [degreeHalf_covariant_derivative_zero] at hh
    simpa only [H,ContinuousLinearMap.zero_comp,ContinuousLinearMap.comp_zero] using hh
  · obtain ⟨N,hN,hNN⟩ := R.jet a y hy i
    refine ⟨N,hN,hNN.trans (mul_le_mul_of_nonneg_right ?_ (Real.sqrt_nonneg _))⟩
    dsimp only [C1]
    linarith only [hCE1]
  · obtain ⟨N,hN,hNN⟩ := E.jet a y hy i
    refine ⟨N,hN,hNN.trans (mul_le_mul_of_nonneg_right ?_ (Real.sqrt_nonneg _))⟩
    dsimp only [C1]
    linarith only [hCR1]

end ShrinkingSpheres.ParallelEnergy
