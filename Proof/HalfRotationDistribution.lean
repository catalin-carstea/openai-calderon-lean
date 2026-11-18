import Proof.SphereSobolevOperatorExt
import Proof.RotationGraphHarmonicBlocks
import Proof.Archive.SphereSobolevSingleRotationAngleDerivative
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped InnerProductSpace
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.SphereHarmonic
open OAI.AnisotropicCalderon.SmoothSphereRotationProjection

/-- Exact physical half-endpoint blocks imply the full distributional
rotation graph needed by the higher-endpoint reconstruction. -/
lemma half_rotation_distribution_of_physical_blocks (i j : I)
    (A C : SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ)))
    (hBlocks : ∀ m n : ℕ,∀ z : harmonicSphereSubspace n,
      sphereSobolevCoefficientL (-(1/2:ℝ)) m (C (sphereSobolevSingleL (1/2:ℝ) n z))=
        harmonicSphereRotation m i j
          (sphereSobolevCoefficientL (-(1/2:ℝ)) m (A (sphereSobolevSingleL (1/2:ℝ) n z)))-
        sphereSobolevCoefficientL (-(1/2:ℝ)) m
          (A (sphereSobolevSingleL (1/2:ℝ) n (harmonicSphereRotation n i j z))))
    (u : SphereSobolev (3/2:ℝ)) :
    sphereSobolevInclusionL (-(1/2:ℝ)) (-(3/2:ℝ)) (by norm_num)
      (A (sphereSobolevRotationL (3/2:ℝ) i j u)+
        C (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num) u))=
      sphereSobolevRotationL (-(1/2:ℝ)) i j
        (A (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num) u)) := by
  let L := (sphereSobolevInclusionL (-(1/2:ℝ)) (-(3/2:ℝ)) (by norm_num)).comp
    (A.comp (sphereSobolevRotationL (3/2:ℝ) i j)+
      C.comp (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)))
  let R := (sphereSobolevRotationL (-(1/2:ℝ)) i j).comp
    (A.comp (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)))
  have hOp : L=R := sphereSobolev_clm_ext_on_single (3/2:ℝ) L R (by
    intro n z
    apply sphereSobolev_ext (-(3/2:ℝ))
    intro m
    have hIncl := sphereSobolevInclusionL_single (3/2:ℝ) (1/2:ℝ) (by norm_num) n z
    have hSingle : sphereSobolevRotationL (3/2:ℝ) i j (sphereSobolevSingleL (3/2:ℝ) n z)=
        sphereSobolevSingleL (1/2:ℝ) n (harmonicSphereRotation n i j z) := by
      simpa only [sphereSobolevSingleL,show (3/2:ℝ)-1=(1/2:ℝ) by norm_num] using
        sphereSobolevRotationL_single (3/2:ℝ) i j n z
    have hRot (v : SphereSobolev (-(1/2:ℝ))) :
        sphereSobolevCoefficientL (-(3/2:ℝ)) m (sphereSobolevRotationL (-(1/2:ℝ)) i j v)=
          harmonicSphereRotation m i j (sphereSobolevCoefficientL (-(1/2:ℝ)) m v) := by
      simpa only [sphereSobolevCoefficientL,show (-(1/2:ℝ))-1=(-(3/2:ℝ)) by norm_num] using
        sphereSobolevCoefficientL_rotation (-(1/2:ℝ)) i j m v
    change sphereSobolevCoefficientL (-(3/2:ℝ)) m
      (sphereSobolevInclusionL (-(1/2:ℝ)) (-(3/2:ℝ)) (by norm_num)
        (A (sphereSobolevRotationL (3/2:ℝ) i j (sphereSobolevSingleL (3/2:ℝ) n z))+
          C (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num) (sphereSobolevSingleL (3/2:ℝ) n z)))) =
      sphereSobolevCoefficientL (-(3/2:ℝ)) m
        (sphereSobolevRotationL (-(1/2:ℝ)) i j
          (A (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num) (sphereSobolevSingleL (3/2:ℝ) n z))))
    rw [hIncl,hSingle,hRot,sphereSobolevCoefficientL_inclusion,map_add]
    exact (add_comm _ _).trans (eq_sub_iff_add_eq.mp (hBlocks m n z)))
  exact DFunLike.congr_fun hOp u
end ShrinkingSpheres
