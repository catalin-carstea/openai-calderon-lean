import Proof.ParallelFirstPotentialCubic

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2800000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
open Set
open scoped ContDiff Topology InnerProductSpace
namespace ShrinkingSpheres.ParallelEnergy
open OAI.AnisotropicCalderon.SphereHarmonic

/-- The complete first-word contraction of the order-dropped cubic has
only the original positive-half horizontal norm and H3/2 mass norm. -/
theorem firstPotential_cubic_row_point_bound {Y Ω : Set X} {m : ℕ} (hm : 2 ≤ m)
    {K ρ c₀ floor ε CF CT CG CK : ℝ} {M : Fin (m+1) → ℝ} {Cj : Fin 9 → ℝ} {d : Data}
    (hY : IsOpen Y) (P : PhysicalPrincipalData Y d CF CT)
    (hd : Admissible Y Ω K ρ c₀ M Cj floor ε d) (hK : 1 ≤ K) (hf : 1 ≤ floor)
    (hε : 0 ≤ ε) (hε1 : ε ≤ 1) {y : X} (hy : y ∈ Y)
    (hCG : 0 ≤ CG) (hCK : 0 ≤ CK) (W : PhysicalPotentialQuarticData P y CG CK)
    (b : I) (u v : SphereSobolev (3/2:ℝ)) :
    let BW := principalModelDegreeCoordinateBudget K (M ⟨1,by omega⟩) (Cj 2)+6+
      3*principalFirstErrorCoordinateTwoJetBudget K |M ⟨1,by omega⟩| |M ⟨2,by omega⟩| (Cj 2)
    let G := max (physicalPotentialGeneratorBudget CF) CG
    let CQ := 49*potentialWordEntryBudget K
    let β := beta d.γ d.radius y
    |∑ a : PhysicalPotentialGeneratorIndex,effectiveFirstWordCoefficient d b y a*
      sphereSobolevDualPairing (1/2:ℝ) (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num) v)
        (firstPotentialNormalizedCubic P W a (PhysicalPrincipalData.potentialWordCoefficient d y) u)| ≤
      (BW*(6*K*G*CK*CQ))*ε^2*(β⁻¹*‖sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num) v‖^2+β*‖u‖^2) := by
  let BW := principalModelDegreeCoordinateBudget K (M ⟨1,by omega⟩) (Cj 2)+6+
    3*principalFirstErrorCoordinateTwoJetBudget K |M ⟨1,by omega⟩| |M ⟨2,by omega⟩| (Cj 2)
  let G := max (physicalPotentialGeneratorBudget CF) CG
  let CQ := 49*potentialWordEntryBudget K
  let CN := 6*K*G*CK*CQ
  let β := beta d.γ d.radius y
  let Jv := sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num) v
  have hG : 0 ≤ G := hCG.trans (le_max_right _ _)
  have hCQ : 0 ≤ CQ := by dsimp only [CQ,potentialWordEntryBudget];positivity
  have hCN : 0 ≤ CN := by dsimp only [CN];positivity
  have hBW : 0 ≤ BW := by
    have hD := principalModelDegreeCoordinateBudget_nonneg K (M ⟨1,by omega⟩) (Cj 2) (zero_le_one.trans hK)
    have hE := principalFirstErrorCoordinateTwoJetBudget_nonneg K |M ⟨1,by omega⟩| |M ⟨2,by omega⟩| (Cj 2)
      (zero_le_one.trans hK) (abs_nonneg _) (abs_nonneg _)
    dsimp only [BW]
    positivity
  have hβ1 : 1 ≤ β := hf.trans (hd.2.2.2.2.1.2 y hy).2.1
  have hβ : 0 < β := zero_lt_one.trans_le hβ1
  have hMass : ∑ a : PhysicalPotentialGeneratorIndex,|effectiveFirstWordCoefficient d b y a| ≤ BW*ε :=
    (effective_first_normalized_word_mass_bound (CF:=CF) (CT:=CT) hm hY hd hK hf hε hε1 hy b).trans
      (div_le_self (mul_nonneg hBW hε) hβ1)
  have hN (a : PhysicalPotentialGeneratorIndex) :
      ‖firstPotentialNormalizedCubic P W a (PhysicalPrincipalData.potentialWordCoefficient d y) u‖ ≤ CN*ε*‖u‖ := by
    have hh := firstPotential_normalized_cubic_norm_bound P hd hK hy hCG hCK W a
      (PhysicalPrincipalData.potentialWordCoefficient d y) u
    have hP := hd.potentialWordMass_le hK hf hε hε1 hy
    exact hh.trans ((mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hP
      (show 0 ≤ 6*K*G*CK by positivity)) (norm_nonneg u)).trans_eq (by dsimp only [CN];ring))
  have hTerm (a : PhysicalPotentialGeneratorIndex) :
      |sphereSobolevDualPairing (1/2:ℝ) Jv
        (firstPotentialNormalizedCubic P W a (PhysicalPrincipalData.potentialWordCoefficient d y) u)| ≤
      ‖Jv‖*(CN*ε*‖u‖) :=
    (abs_sphereSobolevDualPairing_le _ _ _).trans (mul_le_mul_of_nonneg_left (hN a) (norm_nonneg Jv))
  calc
    _ ≤ ∑ a : PhysicalPotentialGeneratorIndex,|effectiveFirstWordCoefficient d b y a*
        sphereSobolevDualPairing (1/2:ℝ) Jv
          (firstPotentialNormalizedCubic P W a (PhysicalPrincipalData.potentialWordCoefficient d y) u)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ a : PhysicalPotentialGeneratorIndex,|effectiveFirstWordCoefficient d b y a| *(‖Jv‖*(CN*ε*‖u‖)) := by
      apply Finset.sum_le_sum
      intro a _
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (hTerm a) (abs_nonneg _)
    _ = (∑ a : PhysicalPotentialGeneratorIndex,|effectiveFirstWordCoefficient d b y a|)*(‖Jv‖*(CN*ε*‖u‖)) :=
      (Finset.sum_mul _ _ _).symm
    _ ≤ (BW*ε)*(‖Jv‖*(CN*ε*‖u‖)) := mul_le_mul_of_nonneg_right hMass (by positivity)
    _ = (BW*CN)*ε^2*(‖Jv‖*‖u‖) := by ring
    _ ≤ (BW*CN)*ε^2*(β⁻¹*‖Jv‖^2+β*‖u‖^2) :=
      mul_le_mul_of_nonneg_left (weighted_product_le ‖Jv‖ ‖u‖ β hβ) (by positivity)

end ShrinkingSpheres.ParallelEnergy
