import Proof.PhysicalHarmonicBlockCasimir
import Proof.RadialRotationCommutator

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set
open scoped ContDiff Topology InnerProductSpace
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.SphereHarmonic
open OAI.AnisotropicCalderon.SmoothSphereRotationProjection

/-- The actual distributional rotation graph already proved for native DN
    remainders gives exactly the SAME physical harmonic commutator blocks. -/
theorem coarsePhysicalHarmonicBlock_of_rotation_distribution (i j : I)
    (R C : SphereSobolev 1 →L[ℝ] SphereSobolev 0)
    (hGraph : ∀ f : SphereSobolev 2,
      sphereSobolevRotationL 0 i j (R (sphereSobolevInclusionL 2 1 (by norm_num) f)) =
        sphereSobolevInclusionL 0 (-1) (by norm_num)
          (C (sphereSobolevInclusionL 2 1 (by norm_num) f)+R (sphereSobolevRotationL 2 i j f)))
    (m n : ℕ) (z : harmonicSphereSubspace n) :
    coarsePhysicalHarmonicBlock C m n z =
      harmonicSphereRotation m i j (coarsePhysicalHarmonicBlock R m n z)-
        coarsePhysicalHarmonicBlock R m n (harmonicSphereRotation n i j z) := by
  have hSingleIncl : sphereSobolevInclusionL 2 1 (by norm_num) (sphereSobolevSingleL 2 n z) =
      sphereSobolevSingleL 1 n z := sphereSobolevInclusionL_single 2 1 (by norm_num) n z
  have hSingleRot : sphereSobolevRotationL 2 i j (sphereSobolevSingleL 2 n z) =
      sphereSobolevSingleL 1 n (harmonicSphereRotation n i j z) := by
    apply sphereSobolev_ext 1
    intro k
    have hh := sphereSobolevCoefficientL_rotation 2 i j k (sphereSobolevSingleL 2 n z)
    by_cases hk : k=n
    · subst k
      rw [sphereSobolevCoefficientL_single_self]
      rw [sphereSobolevCoefficientL_single_self] at hh
      simpa only [sphereSobolevCoefficientL,show (2:ℝ)-1=1 by norm_num] using hh
    · rw [sphereSobolevCoefficientL_single_ne _ _ _ hk]
      rw [sphereSobolevCoefficientL_single_ne _ _ _ hk,map_zero] at hh
      simpa only [sphereSobolevCoefficientL,show (2:ℝ)-1=1 by norm_num] using hh
  have hh := congrArg (sphereSobolevCoefficientL (-1) m) (hGraph (sphereSobolevSingleL 2 n z))
  rw [hSingleIncl,hSingleRot] at hh
  have hRot : sphereSobolevCoefficientL (-1) m (sphereSobolevRotationL 0 i j
      (R (sphereSobolevSingleL 1 n z))) =
      harmonicSphereRotation m i j (sphereSobolevCoefficientL 0 m (R (sphereSobolevSingleL 1 n z))) := by
    simpa only [sphereSobolevCoefficientL,show (0:ℝ)-1=(-1) by norm_num] using
      sphereSobolevCoefficientL_rotation 0 i j m (R (sphereSobolevSingleL 1 n z))
  rw [hRot,sphereSobolevCoefficientL_inclusion,map_add] at hh
  change coarsePhysicalHarmonicBlock C m n z = _
  change harmonicSphereRotation m i j (coarsePhysicalHarmonicBlock R m n z) =
    coarsePhysicalHarmonicBlock C m n z+coarsePhysicalHarmonicBlock R m n (harmonicSphereRotation n i j z) at hh
  exact eq_sub_of_add_eq hh.symm

end ShrinkingSpheres
