import Proof.RadialRotationCommutator

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 700000
open scoped Topology
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.SphereHarmonic

/-- The distributional graph on dense H2 data uniquely specifies a bounded
    H1-to-L2 angular commutator of the same actual remainder. -/
theorem radial_rotation_commutator_unique (i j : I)
    (P C D : SphereSobolev 1 →L[ℝ] SphereSobolev 0)
    (hC : ∀ f : SphereSobolev 2,sphereSobolevRotationL 0 i j (P (sphereSobolevInclusionL 2 1 (by norm_num) f)) =
      sphereSobolevInclusionL 0 (-1) (by norm_num) (C (sphereSobolevInclusionL 2 1 (by norm_num) f)+P (sphereSobolevRotationL 2 i j f)))
    (hD : ∀ f : SphereSobolev 2,sphereSobolevRotationL 0 i j (P (sphereSobolevInclusionL 2 1 (by norm_num) f)) =
      sphereSobolevInclusionL 0 (-1) (by norm_num) (D (sphereSobolevInclusionL 2 1 (by norm_num) f)+P (sphereSobolevRotationL 2 i j f))) : C = D := by
  apply DFunLike.ext'
  apply (denseRange_sphereSobolevInclusionL 2 1 (by norm_num)).equalizer C.continuous D.continuous
  funext f
  have hGraph := (hC f).symm.trans (hD f)
  have hSame := sphereSobolevInclusionL_injective 0 (-1) (by norm_num) hGraph
  exact add_right_cancel hSame

end ShrinkingSpheres
