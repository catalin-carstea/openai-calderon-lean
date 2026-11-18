import Proof.HigherScalarAdjointRemainderEndpoints
import Proof.FiniteScalarRemainderNorms
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxSynthPendingDepth 30
set_option maxRecDepth 2400
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.DirichletFamily OAI.AnisotropicCalderon.SphereHarmonic

lemma norm_taylorScalarAdjointRemainderHigherL_weighted
    (KH : SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (3/2:ℝ))
    (C : TaylorGeneratorIndex → SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (3/2:ℝ))
    (Q : TaylorGeneratorIndex → ClosedCoefficientJets 3) (B : TaylorGeneratorIndex → ℝ)
    (CK CN r : ℝ) (hCK : 0 ≤ CK) (hKH : ‖KH‖ ≤ CK*r^2)
    (hB : ∀ a,‖Q a‖ ≤ B a)
    (hC : ∀ a,‖C a‖ ≤ CN*(taylorGeneratorWeight r a*B a)) :
    ‖taylorScalarAdjointRemainderHigherL KH C Q‖ ≤
      (‖closedThreeJetHigherScalarMultiplierL‖*CK+CN)*(∑ a,taylorGeneratorWeight r a*B a) := by
  have hSum := norm_finite_scalar_remainder_le closedThreeJetHigherScalarMultiplierL
    (taylorGeneratorAdjointDefectHigherL KH) C Q TaylorGeneratorIndex.adjointSign
    (fun a => by cases a <;> norm_num [TaylorGeneratorIndex.adjointSign])
  apply hSum.trans
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro a _
  have hM : ‖closedThreeJetHigherScalarMultiplierL‖*‖Q a‖ ≤
      ‖closedThreeJetHigherScalarMultiplierL‖*B a :=
    mul_le_mul_of_nonneg_left (hB a) (norm_nonneg _)
  have hMB : 0 ≤ ‖closedThreeJetHigherScalarMultiplierL‖*B a :=
    mul_nonneg (norm_nonneg _) ((norm_nonneg _).trans (hB a))
  have hh := mul_le_mul hM
    (norm_taylorGeneratorAdjointDefectHigherL_le KH CK r hCK hKH a)
    (norm_nonneg _) hMB
  exact (add_le_add hh (hC a)).trans_eq (by ring)
end ShrinkingSpheres
