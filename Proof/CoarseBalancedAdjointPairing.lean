import Proof.LowBoundedCorrectionAdjoint
import Proof.Archive.NativeHarmonicHalfCoarseDualPairing

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped InnerProductSpace
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.SphereHarmonic
open OAI.AnisotropicCalderon.NativeHarmonicHalfCoarseDualPairing

/-- Angular transposition from the genuine coarse forward graph and the
genuine higher adjoint graph. All four inclusions are actual maps. -/
lemma coarse_balanced_adjoint_pairing
    (B : SphereSobolev 1 →L[ℝ] SphereSobolev 0)
    (C : SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ)))
    (A : SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ))
    (hB : (sphereSobolevInclusionL 0 (-(1/2:ℝ)) (by norm_num)).comp B=
      C.comp (sphereSobolevInclusionL 1 (1/2:ℝ) (by norm_num)))
    (hA : (sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)).comp A=
      C.adjoint.comp (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)))
    (u : SphereSobolev (3/2:ℝ)) (v : SphereSobolev 1) :
    ⟪sphereSobolevInclusionL (3/2:ℝ) 0 (by norm_num) u,B v⟫_ℝ=
      sphereSobolevDualPairing (1/2:ℝ) (A u)
        (sphereSobolevInclusionL 0 (-(1/2:ℝ)) (by norm_num)
          (sphereSobolevInclusionL 1 0 (by norm_num) v)) := by
  let Ju := sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num) u
  let Jv := sphereSobolevInclusionL 1 (1/2:ℝ) (by norm_num) v
  let T := sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)
  have hBg := DFunLike.congr_fun hB v
  have hAg := DFunLike.congr_fun hA u
  simp only [ContinuousLinearMap.comp_apply] at hBg hAg
  have hTv : T Jv=sphereSobolevInclusionL 0 (-(1/2:ℝ)) (by norm_num)
      (sphereSobolevInclusionL 1 0 (by norm_num) v) := by
    simp only [T,Jv,sphereSobolevInclusionL_trans_apply]
  calc
    _ = sphereSobolevDualPairing (1/2:ℝ) Ju
        (sphereSobolevInclusionL 0 (-(1/2:ℝ)) (by norm_num) (B v)) := by
      have hh := sphereSobolevDualPairing_zero_inclusion (1/2:ℝ) (by norm_num) Ju (B v)
      simpa only [Ju,sphereSobolevInclusionL_trans_apply] using hh.symm
    _ = ⟪Ju,C Jv⟫_ℝ := congrArg (fun z => sphereSobolevDualPairing (1/2:ℝ) Ju z) hBg
    _ = ⟪C.adjoint Ju,Jv⟫_ℝ := (C.adjoint_inner_left _ _).symm
    _ = ⟪T (A u),Jv⟫_ℝ := congrArg (fun z => ⟪z,Jv⟫_ℝ) hAg.symm
    _ = ⟪A u,T Jv⟫_ℝ := by
      have hh := T.adjoint_inner_right (A u) Jv
      rw [show T.adjoint=T from sphereSobolevHalfNegativeInclusion_adjoint] at hh
      exact hh.symm
    _ = _ := congrArg (fun z => sphereSobolevDualPairing (1/2:ℝ) (A u) z) hTv

end ShrinkingSpheres
