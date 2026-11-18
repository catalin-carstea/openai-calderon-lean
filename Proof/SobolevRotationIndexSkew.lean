import Proof.RotationCoarseAdjointPacket
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1400000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.SphereHarmonic
open OAI.AnisotropicCalderon.SmoothSphereRotationProjection
open OAI.AnisotropicCalderon.SmoothSphereRotation

lemma harmonicSphereRotation_index_swap (n : ℕ) (i j : I) :
    harmonicSphereRotation n i j = -harmonicSphereRotation n j i := by
  apply ContinuousLinearMap.ext
  intro v
  obtain ⟨p,rfl⟩ := harmonicPolynomialSphereMap_surjective n v
  simp only [_root_.neg_apply,harmonicSphereRotation_apply_image]
  apply Subtype.ext
  change polynomialSphereL2 (polynomialRotation i j p) = -polynomialSphereL2 (polynomialRotation j i p)
  rw [← map_neg]
  congr 1
  unfold polynomialRotation
  abel

lemma sphereSobolevRotationL_index_swap (s : ℝ) (i j : I) :
    sphereSobolevRotationL s i j = -sphereSobolevRotationL s j i := by
  apply ContinuousLinearMap.ext
  intro u
  apply sphereSobolev_ext (s-1)
  intro n
  change sphereSobolevCoefficientL (s-1) n (sphereSobolevRotationL s i j u) =
    sphereSobolevCoefficientL (s-1) n (-(sphereSobolevRotationL s j i u))
  rw [map_neg,sphereSobolevCoefficientL_rotation,sphereSobolevCoefficientL_rotation]
  exact congrArg (fun A : harmonicSphereSubspace n →L[ℝ] harmonicSphereSubspace n =>
    A (sphereSobolevCoefficientL s n u)) (harmonicSphereRotation_index_swap n i j)
end ShrinkingSpheres
