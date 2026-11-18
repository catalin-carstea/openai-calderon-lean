import Proof.CoarseAngularFieldBudgets
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped BigOperators
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.DirichletFamily
open OAI.AnisotropicCalderon.SphereHarmonic

def closedScalarRotationJetBudget : ℝ :=
  ‖closedOneBoundaryScalarMultiplierL‖+‖closedThreeJetCoarseScalarMultiplierL‖+
    (∑ ij : I × I,‖closedCoefficientAngularOneL ij.1 ij.2‖)+
    (∑ ij : I × I,‖closedCoefficientAngularCoarseL ij.1 ij.2‖)

lemma closedScalarRotationJetBudget_nonneg : 0 ≤ closedScalarRotationJetBudget := by
  unfold closedScalarRotationJetBudget
  positivity

lemma closedCoefficient_scalar_rotation_jet_bound
    {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    {Q : P → ClosedCoefficientJets 3} {p : P} {N : ℕ} {B : ℝ}
    (hQ : SmoothFiniteJetBound Q p N B) :
    ScalarRotationMultiplierData.JetBound (fun x => scalarRotationDataOfClosedCoefficient (Q x)) p N
      (closedScalarRotationJetBudget*B) := by
  obtain ⟨h1,h2,h3,h4⟩ := four_block_budget_bounds
    ‖closedOneBoundaryScalarMultiplierL‖ ‖closedThreeJetCoarseScalarMultiplierL‖
    (fun ij => ‖closedCoefficientAngularOneL ij.1 ij.2‖)
    (fun ij => ‖closedCoefficientAngularCoarseL ij.1 ij.2‖)
    (norm_nonneg _) (norm_nonneg _) (fun _ => norm_nonneg _) (fun _ => norm_nonneg _)
  exact ⟨(hQ.clm closedOneBoundaryScalarMultiplierL).weaken (mul_le_mul_of_nonneg_right h1 hQ.nonneg),
    (hQ.clm closedThreeJetCoarseScalarMultiplierL).weaken (mul_le_mul_of_nonneg_right h2 hQ.nonneg),
    (fun ij => (hQ.clm (closedCoefficientAngularOneL ij.1 ij.2)).weaken
      (mul_le_mul_of_nonneg_right (h3 ij) hQ.nonneg)),
    (fun ij => (hQ.clm (closedCoefficientAngularCoarseL ij.1 ij.2)).weaken
      (mul_le_mul_of_nonneg_right (h4 ij) hQ.nonneg))⟩
end ShrinkingSpheres
