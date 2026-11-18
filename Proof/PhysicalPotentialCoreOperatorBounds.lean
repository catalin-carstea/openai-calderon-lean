import Proof.FiniteQuadraticWordNormBound
import Proof.PotentialFirstWordNormEstimate
import Proof.PotentialFirstWordHigherBounds
import Proof.PhysicalPotentialCoreMeasurability

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2600000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
open Set
open scoped ContDiff Topology
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.SphereHarmonic

lemma continuousOn_potentialWordMass {Y Ω : Set X} {m : ℕ}
    {K ρ c₀ floor ε : ℝ} {M : Fin (m+1) → ℝ} {Cj : Fin 9 → ℝ} {d : Data}
    (hY : IsOpen Y) (hSub : Y ⊆ Ω) (hd : Admissible Y Ω K ρ c₀ M Cj floor ε d) (hK : 0 < K) :
    ContinuousOn (potentialWordMass d) Y := by
  have hw (a : PhysicalPotentialGeneratorIndex) :
      ContinuousOn (fun y => potentialGeneratorWeight (d.radius y) a) Y := by
    rcases a with a|(a|a)
    · exact continuousOn_const
    · exact continuousOn_const
    · exact hd.2.2.2.2.1.1.continuousOn
  exact continuousOn_finsetSum Finset.univ (fun a _ => continuousOn_finsetSum Finset.univ (fun b _ =>
    (((hd.contDiffOn_potentialWordCoefficient hY hSub hK a b).continuousOn.abs).mul (hw a)).mul (hw b)))

namespace PhysicalPrincipalData
variable {Y : Set X} {d : Data} {CF CT CG CK : ℝ}

lemma norm_potentialQuadraticCoreL_le_word_mass (P : PhysicalPrincipalData Y d CF CT)
    {y : X} (hy : y ∈ Y) (W : PhysicalPotentialQuarticData P y CG CK)
    (hCK : 0 ≤ CK) (hr : 0 ≤ d.radius y) :
    ‖P.potentialQuadraticCoreL W‖ ≤
      (physicalPotentialGeneratorBudget CF*(3*physicalPotentialGeneratorBudget CF+CK))*potentialWordMass d y := by
  let BG := physicalPotentialGeneratorBudget CF
  have hBG : 0 ≤ BG := (by norm_num : (0:ℝ) ≤ 2).trans (physicalPotentialGeneratorBudget_bounds CF).1
  have hW := norm_finite_mixed_quadratic_words_le_mass (potentialWordCoefficient d y)
    (P.potentialGeneratorHigh y) W.forwardFirstWordHigherL (potentialGeneratorWeight (d.radius y))
    hBG (show 0 ≤ 3*BG+CK by positivity) (potentialGeneratorWeight_nonneg hr)
    (fun a => (P.potential_generator_norm_bounds hy hr a).2) (W.norm_forwardFirstWordHigherL_le hy hr)
  unfold potentialQuadraticCoreL
  calc
    _ ≤ ‖sphereSobolevInclusionL (1/2:ℝ) 0 (by norm_num)‖*‖∑ a,∑ b,
        potentialWordCoefficient d y a b • (P.potentialGeneratorHigh y a).comp (W.forwardFirstWordHigherL b)‖ :=
      ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ 1*‖∑ a,∑ b,potentialWordCoefficient d y a b •
        (P.potentialGeneratorHigh y a).comp (W.forwardFirstWordHigherL b)‖ :=
      mul_le_mul_of_nonneg_right (norm_sphereSobolevInclusionL_le (1/2:ℝ) 0 (by norm_num)) (norm_nonneg _)
    _ ≤ _ := by simpa only [one_mul,potentialWordMass,potentialWordWeightedEntry] using hW

lemma norm_potentialQuadraticAdjointCoreL_le_word_mass (P : PhysicalPrincipalData Y d CF CT)
    {y : X} (W : PhysicalPotentialQuarticData P y CG CK)
    (hCG : 0 ≤ CG) (hCK : 0 ≤ CK) (hr : 0 ≤ d.radius y) :
    ‖P.potentialQuadraticAdjointCoreL W‖ ≤ (CG*(3*CG+CK))*potentialWordMass d y := by
  have hW := norm_finite_mixed_quadratic_words_le_mass (fun b a => potentialWordCoefficient d y a b)
    W.adjointHigh W.reverseFirstWordHigherL (potentialGeneratorWeight (d.radius y))
    hCG (show 0 ≤ 3*CG+CK by positivity) (potentialGeneratorWeight_nonneg hr)
    W.adjoint_bound (W.norm_reverseFirstWordHigherL_le hCG hCK hr)
  have hMass : (∑ b : PhysicalPotentialGeneratorIndex,∑ a : PhysicalPotentialGeneratorIndex,
      |potentialWordCoefficient d y a b| *potentialGeneratorWeight (d.radius y) b*
        potentialGeneratorWeight (d.radius y) a)=potentialWordMass d y := by
    unfold potentialWordMass potentialWordWeightedEntry
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro b _
    ring
  rw [hMass] at hW
  have hWords : (∑ a : PhysicalPotentialGeneratorIndex,∑ b : PhysicalPotentialGeneratorIndex,
      potentialWordCoefficient d y a b • (W.adjointHigh b).comp (W.reverseFirstWordHigherL a))=
      ∑ b : PhysicalPotentialGeneratorIndex,∑ a : PhysicalPotentialGeneratorIndex,
        potentialWordCoefficient d y a b • (W.adjointHigh b).comp (W.reverseFirstWordHigherL a) := Finset.sum_comm
  unfold potentialQuadraticAdjointCoreL
  rw [hWords]
  calc
    _ ≤ ‖sphereSobolevInclusionL (1/2:ℝ) 0 (by norm_num)‖*‖∑ b,∑ a,
        potentialWordCoefficient d y a b • (W.adjointHigh b).comp (W.reverseFirstWordHigherL a)‖ :=
      ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ 1*‖∑ b,∑ a,potentialWordCoefficient d y a b •
        (W.adjointHigh b).comp (W.reverseFirstWordHigherL a)‖ :=
      mul_le_mul_of_nonneg_right (norm_sphereSobolevInclusionL_le (1/2:ℝ) 0 (by norm_num)) (norm_nonneg _)
    _ ≤ _ := by simpa only [one_mul] using hW

end PhysicalPrincipalData
end ShrinkingSpheres
