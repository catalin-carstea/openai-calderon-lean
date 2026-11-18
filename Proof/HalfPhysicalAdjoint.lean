import Proof.RadialDegreeCommutatorAdjoint
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped InnerProductSpace
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.SphereHarmonic

/-- The LP transpose of a half-order realization is exactly the physical
    probability-L2 adjoint realization, with the same coefficient witnesses. -/
theorem half_operator_adjoint_physical_block
    (R Ra : SphereSobolev 1 →L[ℝ] SphereSobolev 0)
    (hPair : ∀ u v : SphereSobolev 1,
      ⟪R u,sphereSobolevInclusionL 1 0 (by norm_num) v⟫_ℝ =
        ⟪sphereSobolevInclusionL 1 0 (by norm_num) u,Ra v⟫_ℝ)
    (L : SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ)))
    (hL : ∀ m n : ℕ,∀ z : harmonicSphereSubspace n,
      sphereSobolevCoefficientL (-(1/2:ℝ)) m (L (sphereSobolevSingleL (1/2:ℝ) n z)) =
        coarsePhysicalHarmonicBlock R m n z)
    (m n : ℕ) (z : harmonicSphereSubspace n) :
    sphereSobolevCoefficientL (-(1/2:ℝ)) m
      (L.adjoint (sphereSobolevSingleL (1/2:ℝ) n z)) = coarsePhysicalHarmonicBlock Ra m n z := by
  apply ext_inner_right ℝ
  intro v
  rw [← sphereSobolevDualPairing_single_left_physical]
  change ⟪sphereSobolevSingleL (1/2:ℝ) m v,L.adjoint (sphereSobolevSingleL (1/2:ℝ) n z)⟫_ℝ = _
  rw [L.adjoint_inner_right,real_inner_comm]
  change sphereSobolevDualPairing (1/2:ℝ) (sphereSobolevSingleL (1/2:ℝ) n z)
    (L (sphereSobolevSingleL (1/2:ℝ) m v)) = _
  rw [sphereSobolevDualPairing_single_left_physical,hL,
    coarsePhysicalHarmonicBlock_true_adjoint R Ra hPair,real_inner_comm v]
end ShrinkingSpheres
