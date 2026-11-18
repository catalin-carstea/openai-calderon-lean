import Proof.ScalarDirichletNormalization
import Proof.CoefficientOperatorLocality
import Proof.UniformStrongC1Neighborhood

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.EnergyBridge OAI.AnisotropicCalderon.DirichletFamily
attribute [local irreducible] strongCoefficientOperatorL

/-- Scalar normalization preserves the actual strong inverse and scales its
    norm using the same source operator; exterior representatives are irrelevant. -/
theorem strong_inverse_normalized_coefficient_bound (F G : SmoothCoefficientMatrix 2)
    (c K C : ℝ) (hc : 0 < c) (hK : 0 ≤ K) (hC : 0 ≤ C) (hcK : c ≤ K)
    (hG : (strongDirichletOperator fixedSobolevCalculus 0 G).IsInvertible)
    (hNorm : ‖(strongDirichletOperator fixedSobolevCalculus 0 G).inverse‖ ≤ C)
    (hField : ∀ z ∈ (ballOpens:Set X),coefficientMatrixField 2 F z = c⁻¹ • coefficientMatrixField 2 G z) :
    (strongDirichletOperator fixedSobolevCalculus 0 F).IsInvertible ∧
      ‖(strongDirichletOperator fixedSobolevCalculus 0 F).inverse‖ ≤ K*C := by
  have hEq : strongDirichletOperator fixedSobolevCalculus 0 F =
      c⁻¹ • strongDirichletOperator fixedSobolevCalculus 0 G := by
    have hLocal := strongDirichletOperator_congr_on_ball fixedSobolevCalculus 0 F (c⁻¹ • G) (fun z hz => by
      rw [coefficientMatrixField_smul];exact hField z hz)
    rw [hLocal]
    change (strongCoefficientOperatorL fixedSobolevCalculus 0) (c⁻¹ • G) = _
    exact (strongCoefficientOperatorL fixedSobolevCalculus 0).map_smul _ _
  have hScaled := clm_inverse_const_smul (strongDirichletOperator fixedSobolevCalculus 0 G) c⁻¹ (inv_ne_zero hc.ne') hG
  rw [hEq]
  refine ⟨hScaled.1,?_⟩
  rw [hScaled.2,inv_inv,norm_smul,Real.norm_eq_abs,abs_of_pos hc]
  exact mul_le_mul hcK hNorm (norm_nonneg _) hK

end ShrinkingSpheres
