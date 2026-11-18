import Proof.CoarseAdjointFromSinglePairs
import Proof.RadialDegreeCommutatorAdjoint
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1400000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped InnerProductSpace
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.SphereHarmonic
open OAI.AnisotropicCalderon.SmoothSphereRotationProjection

/-- Distributional rotation commutators of a true adjoint pair are again
    true adjoints on H1, whenever both commutators are bounded there. -/
theorem coarse_rotation_commutators_true_adjoint
    (i j : I) (R Ra C Ca : SphereSobolev 1 →L[ℝ] SphereSobolev 0)
    (hPair : ∀ u v : SphereSobolev 1,
      ⟪R u,sphereSobolevInclusionL 1 0 (by norm_num) v⟫_ℝ =
        ⟪sphereSobolevInclusionL 1 0 (by norm_num) u,Ra v⟫_ℝ)
    (hC : ∀ m n : ℕ,∀ z : harmonicSphereSubspace n,
      coarsePhysicalHarmonicBlock C m n z =
        harmonicSphereRotation m i j (coarsePhysicalHarmonicBlock R m n z)-
          coarsePhysicalHarmonicBlock R m n (harmonicSphereRotation n i j z))
    (hCa : ∀ m n : ℕ,∀ z : harmonicSphereSubspace n,
      coarsePhysicalHarmonicBlock Ca m n z =
        harmonicSphereRotation m i j (coarsePhysicalHarmonicBlock Ra m n z)-
          coarsePhysicalHarmonicBlock Ra m n (harmonicSphereRotation n i j z)) :
    ∀ u v : SphereSobolev 1,
      ⟪C u,sphereSobolevInclusionL 1 0 (by norm_num) v⟫_ℝ =
        ⟪sphereSobolevInclusionL 1 0 (by norm_num) u,Ca v⟫_ℝ := by
  apply coarse_operator_adjoint_pairing_of_singles C Ca
  intro m n z w
  have hBlocks : ⟪coarsePhysicalHarmonicBlock C m n z,w⟫_ℝ =
      ⟪z,coarsePhysicalHarmonicBlock Ca n m w⟫_ℝ := by
    rw [hC,hCa,inner_sub_left,inner_sub_right,inner_harmonicSphereRotation_skew,
      coarsePhysicalHarmonicBlock_true_adjoint R Ra hPair,
      coarsePhysicalHarmonicBlock_true_adjoint R Ra hPair]
    rw [inner_harmonicSphereRotation_skew]
    ring
  calc
    _ = ⟪coarsePhysicalHarmonicBlock C m n z,w⟫_ℝ :=
      (coarsePhysicalHarmonicBlock_sobolev_pairing C m n z w).symm
    _ = ⟪z,coarsePhysicalHarmonicBlock Ca n m w⟫_ℝ := hBlocks
    _ = ⟪coarsePhysicalHarmonicBlock Ca n m w,z⟫_ℝ := real_inner_comm _ _
    _ = _ := (coarsePhysicalHarmonicBlock_sobolev_pairing Ca n m w z).trans (real_inner_comm _ _)
end ShrinkingSpheres
