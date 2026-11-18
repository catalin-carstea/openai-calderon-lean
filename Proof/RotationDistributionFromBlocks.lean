import Proof.SphereSobolevOperatorExt
import Proof.RotationGraphHarmonicBlocks
import Proof.Archive.SphereSobolevSingleRotationAngleDerivative
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped InnerProductSpace
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.SphereHarmonic
open OAI.AnisotropicCalderon.SmoothSphereRotationProjection

/-- Exact physical harmonic block identities imply the full coarse
    distributional rotation graph, by density of physical single modes. -/
theorem rotation_distribution_of_physical_blocks (i j : I)
    (A C : SphereSobolev 1 →L[ℝ] SphereSobolev 0)
    (hBlocks : ∀ m n : ℕ,∀ z : harmonicSphereSubspace n,
      coarsePhysicalHarmonicBlock C m n z =
        harmonicSphereRotation m i j (coarsePhysicalHarmonicBlock A m n z)-
          coarsePhysicalHarmonicBlock A m n (harmonicSphereRotation n i j z))
    (f : SphereSobolev 2) :
    sphereSobolevRotationL 0 i j (A (sphereSobolevInclusionL 2 1 (by norm_num) f)) =
      sphereSobolevInclusionL 0 (-1) (by norm_num)
        (C (sphereSobolevInclusionL 2 1 (by norm_num) f)+A (sphereSobolevRotationL 2 i j f)) := by
  let L := (sphereSobolevRotationL 0 i j).comp (A.comp (sphereSobolevInclusionL 2 1 (by norm_num)))
  let R := (sphereSobolevInclusionL 0 (-1) (by norm_num)).comp
    (C.comp (sphereSobolevInclusionL 2 1 (by norm_num))+A.comp (sphereSobolevRotationL 2 i j))
  have hOp : L = R := sphereSobolev_clm_ext_on_single 2 L R (by
    intro n z
    apply sphereSobolev_ext (-1)
    intro m
    have hIncl := sphereSobolevInclusionL_single 2 1 (by norm_num) n z
    have hSingle : sphereSobolevRotationL 2 i j (sphereSobolevSingleL 2 n z) =
        sphereSobolevSingleL 1 n (harmonicSphereRotation n i j z) := by
      simpa only [sphereSobolevSingleL,show (2:ℝ)-1=1 by norm_num] using
        sphereSobolevRotationL_single 2 i j n z
    have hRot (u : SphereSobolev 0) :
        sphereSobolevCoefficientL (-1:ℝ) m (sphereSobolevRotationL 0 i j u) =
          harmonicSphereRotation m i j (sphereSobolevCoefficientL 0 m u) := by
      simpa only [sphereSobolevCoefficientL,show (0:ℝ)-1=-1 by norm_num] using
        sphereSobolevCoefficientL_rotation 0 i j m u
    change sphereSobolevCoefficientL (-1:ℝ) m
      (sphereSobolevRotationL 0 i j (A (sphereSobolevInclusionL 2 1 (by norm_num) (sphereSobolevSingleL 2 n z)))) =
      sphereSobolevCoefficientL (-1:ℝ) m
        (sphereSobolevInclusionL 0 (-1) (by norm_num)
          (C (sphereSobolevInclusionL 2 1 (by norm_num) (sphereSobolevSingleL 2 n z))+
            A (sphereSobolevRotationL 2 i j (sphereSobolevSingleL 2 n z))))
    rw [hIncl,hSingle,hRot,sphereSobolevCoefficientL_inclusion,map_add]
    exact (eq_sub_iff_add_eq.mp (hBlocks m n z)).symm)
  exact congrArg (fun T : SphereSobolev 2 →L[ℝ] SphereSobolev (-1:ℝ) => T f) hOp
end ShrinkingSpheres
