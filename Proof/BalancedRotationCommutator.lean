import Proof.UniformActualAngularEndpoints
import Proof.Archive.SphereSobolevConormalRotationDerivative
import Proof.DenseOperatorRestrictionUnique
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxSynthPendingDepth 30
set_option maxRecDepth 2200
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.SphereHarmonic

/-- A coarse physical rotation graph and compatible SAME endpoints give
    the exact balanced commutator graph on the full higher endpoint. -/
lemma balanced_rotation_commutator (i j : I)
    (E S : SphereSobolev 1 →L[ℝ] SphereSobolev 0)
    (Lo C : SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ)))
    (Hi : SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ))
    (hLo : (sphereSobolevInclusionL 0 (-(1/2:ℝ)) (by norm_num)).comp E=
      Lo.comp (sphereSobolevInclusionL 1 (1/2:ℝ) (by norm_num)))
    (hHi : (sphereSobolevInclusionL (1/2:ℝ) 0 (by norm_num)).comp Hi=
      E.comp (sphereSobolevInclusionL (3/2:ℝ) 1 (by norm_num)))
    (hC : (sphereSobolevInclusionL 0 (-(1/2:ℝ)) (by norm_num)).comp S=
      C.comp (sphereSobolevInclusionL 1 (1/2:ℝ) (by norm_num)))
    (hGraph : ∀ u : SphereSobolev 2,
      sphereSobolevRotationL 0 i j (E (sphereSobolevInclusionL 2 1 (by norm_num) u))=
        sphereSobolevInclusionL 0 (-1) (by norm_num)
          (S (sphereSobolevInclusionL 2 1 (by norm_num) u)+E (sphereSobolevRotationL 2 i j u))) :
    (sphereSobolevRotationL (1/2:ℝ) i j).comp Hi-Lo.comp (sphereSobolevRotationL (3/2:ℝ) i j)=
      C.comp (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)) := by
  apply clm_eq_of_dense_restriction (sphereSobolevInclusionL 2 (3/2:ℝ) (by norm_num))
    (denseRange_sphereSobolevInclusionL 2 (3/2:ℝ) (by norm_num))
  apply ContinuousLinearMap.ext
  intro u
  apply sphereSobolevInclusionL_injective (-(1/2:ℝ)) (-1) (by norm_num)
  have hRotLow (w : SphereSobolev (1/2:ℝ)) :
      sphereSobolevInclusionL (-(1/2:ℝ)) (-1) (by norm_num) (sphereSobolevRotationL (1/2:ℝ) i j w)=
        sphereSobolevRotationL 0 i j (sphereSobolevInclusionL (1/2:ℝ) 0 (by norm_num) w) := by
    have h := sphereSobolevRotationL_inclusion (1/2:ℝ) 0 (by norm_num) i j
    have hI : sphereSobolevInclusionL ((1/2:ℝ)-1) ((0:ℝ)-1) (by norm_num)=
        sphereSobolevInclusionL (-(1/2:ℝ)) (-1) (by norm_num) := by congr 1 <;> norm_num
    rw [hI] at h
    exact (DFunLike.congr_fun h w).symm
  have hRotHigh : sphereSobolevRotationL (3/2:ℝ) i j (sphereSobolevInclusionL 2 (3/2:ℝ) (by norm_num) u)=
      sphereSobolevInclusionL 1 (1/2:ℝ) (by norm_num) (sphereSobolevRotationL 2 i j u) := by
    have h := sphereSobolevRotationL_inclusion 2 (3/2:ℝ) (by norm_num) i j
    have hI : sphereSobolevInclusionL ((2:ℝ)-1) ((3/2:ℝ)-1) (by norm_num)=
        sphereSobolevInclusionL 1 (1/2:ℝ) (by norm_num) := by congr 1 <;> norm_num
    rw [hI] at h
    exact DFunLike.congr_fun h u
  have hLoP (w : SphereSobolev 1) : Lo (sphereSobolevInclusionL 1 (1/2:ℝ) (by norm_num) w)=
      sphereSobolevInclusionL 0 (-(1/2:ℝ)) (by norm_num) (E w) := (DFunLike.congr_fun hLo w).symm
  have hHiP : sphereSobolevInclusionL (1/2:ℝ) 0 (by norm_num)
      (Hi (sphereSobolevInclusionL 2 (3/2:ℝ) (by norm_num) u))=
        E (sphereSobolevInclusionL 2 1 (by norm_num) u) := by
    have h := DFunLike.congr_fun hHi (sphereSobolevInclusionL 2 (3/2:ℝ) (by norm_num) u)
    change sphereSobolevInclusionL (1/2:ℝ) 0 (by norm_num)
      (Hi (sphereSobolevInclusionL 2 (3/2:ℝ) (by norm_num) u))=
      E (sphereSobolevInclusionL (3/2:ℝ) 1 (by norm_num)
        (sphereSobolevInclusionL 2 (3/2:ℝ) (by norm_num) u)) at h
    rw [sphereSobolevInclusionL_trans_apply] at h
    exact h
  have hCP : C (sphereSobolevInclusionL 2 (1/2:ℝ) (by norm_num) u)=
      sphereSobolevInclusionL 0 (-(1/2:ℝ)) (by norm_num) (S (sphereSobolevInclusionL 2 1 (by norm_num) u)) := by
    have h := (DFunLike.congr_fun hC (sphereSobolevInclusionL 2 1 (by norm_num) u)).symm
    change C (sphereSobolevInclusionL 1 (1/2:ℝ) (by norm_num)
      (sphereSobolevInclusionL 2 1 (by norm_num) u))=
      sphereSobolevInclusionL 0 (-(1/2:ℝ)) (by norm_num)
        (S (sphereSobolevInclusionL 2 1 (by norm_num) u)) at h
    rw [sphereSobolevInclusionL_trans_apply] at h
    exact h
  simp only [ContinuousLinearMap.comp_apply,_root_.sub_apply,map_sub,hRotLow,hRotHigh,
    hLoP,hHiP,sphereSobolevInclusionL_trans_apply,hCP]
  have h := hGraph u
  rw [map_add] at h
  exact sub_eq_iff_eq_add.mpr h
end ShrinkingSpheres
