import Proof.Archive.NativeHarmonicHalfCoarseDualPairing
import Proof.ActualRadialTaylorEndpoints
import Mathlib.Analysis.InnerProductSpace.Adjoint
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped InnerProductSpace
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.SphereHarmonic
open OAI.AnisotropicCalderon.NativeHarmonicHalfCoarseDualPairing
local instance negativeTransposeComplete : CompleteSpace (SphereSobolev (-(1/2:ℝ))) := lp.completeSpace
lemma negative_half_transpose_graph (T Ta : SphereSobolev 1 →L[ℝ] SphereSobolev 0)
    (KN : SphereSobolev (-(1/2:ℝ)) →L[ℝ] SphereSobolev (-(1/2:ℝ)))
    (hPair : ∀ u v : SphereSobolev 1,
      ⟪T u,sphereSobolevInclusionL 1 0 (by norm_num) v⟫_ℝ=
      ⟪sphereSobolevInclusionL 1 0 (by norm_num) u,Ta v⟫_ℝ)
    (hGraph : (sphereSobolevInclusionL 0 (-(1/2:ℝ)) (by norm_num)).comp T=
      KN.comp (sphereSobolevInclusionL 1 (-(1/2:ℝ)) (by norm_num))) :
    (sphereSobolevInclusionL (1/2:ℝ) 0 (by norm_num)).comp
      ((KN.adjoint : SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ)).comp
        (sphereSobolevInclusionL 1 (1/2:ℝ) (by norm_num)))=Ta := by
  apply ContinuousLinearMap.ext
  intro u
  have hTest (v : SphereSobolev 1) :
      ⟪sphereSobolevInclusionL (1/2:ℝ) 0 (by norm_num)
        (KN.adjoint (sphereSobolevInclusionL 1 (1/2:ℝ) (by norm_num) u)),
        sphereSobolevInclusionL 1 0 (by norm_num) v⟫_ℝ=
      ⟪Ta u,sphereSobolevInclusionL 1 0 (by norm_num) v⟫_ℝ := by
    have hg := congrArg (fun A : SphereSobolev 1 →L[ℝ] SphereSobolev (-(1/2:ℝ)) => A v) hGraph
    change sphereSobolevInclusionL 0 (-(1/2:ℝ)) (by norm_num) (T v)=
      KN (sphereSobolevInclusionL 1 (-(1/2:ℝ)) (by norm_num) v) at hg
    have hI := sphereSobolevInclusionL_trans_apply 1 0 (-(1/2:ℝ)) (by norm_num) (by norm_num) v
    have hJ := sphereSobolevInclusionL_trans_apply 1 (1/2:ℝ) 0 (by norm_num) (by norm_num) u
    calc
      _ = sphereSobolevDualPairing (1/2:ℝ)
          (KN.adjoint (sphereSobolevInclusionL 1 (1/2:ℝ) (by norm_num) u))
          (sphereSobolevInclusionL 1 (-(1/2:ℝ)) (by norm_num) v) := by
        exact (sphereSobolevDualPairing_zero_inclusion (1/2:ℝ) (by norm_num)
          (KN.adjoint (sphereSobolevInclusionL 1 (1/2:ℝ) (by norm_num) u))
          (sphereSobolevInclusionL 1 0 (by norm_num) v)).symm.trans
            (congrArg (sphereSobolevDualPairing (1/2:ℝ)
              (KN.adjoint (sphereSobolevInclusionL 1 (1/2:ℝ) (by norm_num) u))) hI)
      _ = sphereSobolevDualPairing (1/2:ℝ) (sphereSobolevInclusionL 1 (1/2:ℝ) (by norm_num) u)
          (KN (sphereSobolevInclusionL 1 (-(1/2:ℝ)) (by norm_num) v)) := KN.adjoint_inner_left _ _
      _ = sphereSobolevDualPairing (1/2:ℝ) (sphereSobolevInclusionL 1 (1/2:ℝ) (by norm_num) u)
          (sphereSobolevInclusionL 0 (-(1/2:ℝ)) (by norm_num) (T v)) := congrArg (sphereSobolevDualPairing (1/2:ℝ) (sphereSobolevInclusionL 1 (1/2:ℝ) (by norm_num) u)) hg.symm
      _ = ⟪sphereSobolevInclusionL 1 0 (by norm_num) u,T v⟫_ℝ := by
        exact (sphereSobolevDualPairing_zero_inclusion (1/2:ℝ) (by norm_num)
          (sphereSobolevInclusionL 1 (1/2:ℝ) (by norm_num) u) (T v)).trans
            (congrArg (fun w : SphereSobolev 0 => ⟪w,T v⟫_ℝ) hJ)
      _ = _ := (real_inner_comm _ _).trans ((hPair v u).trans (real_inner_comm _ _))
  have hEq := (denseRange_sphereSobolevInclusionL 1 0 (by norm_num)).equalizer
    (continuous_const.inner continuous_id) (continuous_const.inner continuous_id) (funext hTest)
  apply ext_inner_right ℝ
  exact congrFun hEq
end ShrinkingSpheres
