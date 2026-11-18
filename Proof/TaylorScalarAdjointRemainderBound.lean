import Proof.TaylorScalarAdjointNormalForm
import Proof.NativeNegativeScalarGeneratorBounds
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxSynthPendingDepth 30
set_option maxRecDepth 2600
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped InnerProductSpace
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.DirichletFamily OAI.AnisotropicCalderon.SphereHarmonic

lemma norm_taylorScalarAdjointRemainderL_weighted
    (KN : SphereSobolev (-(1/2:ℝ)) →L[ℝ] SphereSobolev (-(1/2:ℝ)))
    (C : TaylorGeneratorIndex → SphereSobolev (-(1/2:ℝ)) →L[ℝ] SphereSobolev (-(1/2:ℝ)))
    (Q : TaylorGeneratorIndex → ClosedCoefficientJets 3)
    (CK CN r : ℝ) (hCK : 0 ≤ CK) (hKN : ‖KN‖ ≤ CK*r^2)
    (hC : ∀ a,‖C a‖ ≤ CN*(taylorGeneratorWeight r a*‖Q a‖)) :
    ‖taylorScalarAdjointRemainderL KN C Q‖ ≤
      (‖closedThreeJetNegativeScalarMultiplierL‖*CK+CN)*
        (∑ a,taylorGeneratorWeight r a*‖Q a‖) := by
  apply (norm_taylorScalarAdjointRemainderL_le KN C Q).trans
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro a _
  have hh := mul_le_mul_of_nonneg_left (norm_taylorGeneratorAdjointDefectL_le KN CK r hCK hKN a)
    (mul_nonneg (norm_nonneg closedThreeJetNegativeScalarMultiplierL) (norm_nonneg (Q a)))
  exact (add_le_add hh (hC a)).trans_eq (by ring)
end ShrinkingSpheres
