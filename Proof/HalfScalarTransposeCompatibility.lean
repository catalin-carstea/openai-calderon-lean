import Proof.NegativeHalfTransposeGraph
import Proof.CompatibleEndpointUniqueness
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped InnerProductSpace
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.SphereHarmonic
open OAI.AnisotropicCalderon.NativeHarmonicHalfCoarseDualPairing

lemma half_dual_pairing_inclusion (u v : SphereSobolev (1/2:ℝ)) :
    sphereSobolevDualPairing (1/2:ℝ) u (sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num) v)=
      ⟪sphereSobolevInclusionL (1/2:ℝ) 0 (by norm_num) u,
        sphereSobolevInclusionL (1/2:ℝ) 0 (by norm_num) v⟫_ℝ := by
  have hh := sphereSobolevDualPairing_zero_inclusion (1/2:ℝ) (by norm_num) u
    (sphereSobolevInclusionL (1/2:ℝ) 0 (by norm_num) v)
  simpa only [sphereSobolevInclusionL_trans_apply] using hh

/-- Two positive-half realizations of a physical coarse adjoint pair give
a compatible negative endpoint by transposition. This retains both witnesses. -/
lemma half_scalar_transpose_compatible
    (T Ta : SphereSobolev 1 →L[ℝ] SphereSobolev 0)
    (C Ca : SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ))
    (hPair : ∀ u v : SphereSobolev 1,
      ⟪T u,sphereSobolevInclusionL 1 0 (by norm_num) v⟫_ℝ=
        ⟪sphereSobolevInclusionL 1 0 (by norm_num) u,Ta v⟫_ℝ)
    (hC : (sphereSobolevInclusionL (1/2:ℝ) 0 (by norm_num)).comp
      (C.comp (sphereSobolevInclusionL 1 (1/2:ℝ) (by norm_num)))=T)
    (hCa : (sphereSobolevInclusionL (1/2:ℝ) 0 (by norm_num)).comp
      (Ca.comp (sphereSobolevInclusionL 1 (1/2:ℝ) (by norm_num)))=Ta) :
    (sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)).comp C=
      Ca.adjoint.comp (sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)) := by
  have hHalf (u v : SphereSobolev (1/2:ℝ)) :
      ⟪sphereSobolevInclusionL (1/2:ℝ) 0 (by norm_num) (C u),sphereSobolevInclusionL (1/2:ℝ) 0 (by norm_num) v⟫_ℝ=
      ⟪sphereSobolevInclusionL (1/2:ℝ) 0 (by norm_num) u,sphereSobolevInclusionL (1/2:ℝ) 0 (by norm_num) (Ca v)⟫_ℝ := by
    have hCore (a b : SphereSobolev 1) :
        ⟪sphereSobolevInclusionL (1/2:ℝ) 0 (by norm_num)
          (C (sphereSobolevInclusionL 1 (1/2:ℝ) (by norm_num) a)),
          sphereSobolevInclusionL (1/2:ℝ) 0 (by norm_num) (sphereSobolevInclusionL 1 (1/2:ℝ) (by norm_num) b)⟫_ℝ=
        ⟪sphereSobolevInclusionL (1/2:ℝ) 0 (by norm_num) (sphereSobolevInclusionL 1 (1/2:ℝ) (by norm_num) a),
          sphereSobolevInclusionL (1/2:ℝ) 0 (by norm_num)
            (Ca (sphereSobolevInclusionL 1 (1/2:ℝ) (by norm_num) b))⟫_ℝ := by
      have hCv := DFunLike.congr_fun hC a
      have hCav := DFunLike.congr_fun hCa b
      simp only [ContinuousLinearMap.comp_apply] at hCv hCav
      rw [hCv,hCav,sphereSobolevInclusionL_trans_apply,sphereSobolevInclusionL_trans_apply]
      exact hPair a b
    exact (denseRange_sphereSobolevInclusionL 1 (1/2:ℝ) (by norm_num)).induction_on₂
      (isClosed_eq (by fun_prop) (by fun_prop)) hCore u v
  apply ContinuousLinearMap.ext
  intro u
  apply ext_inner_left ℝ
  intro v
  change sphereSobolevDualPairing (1/2:ℝ) v
    (sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num) (C u))=
    ⟪v,Ca.adjoint (sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num) u)⟫_ℝ
  rw [Ca.adjoint_inner_right]
  change sphereSobolevDualPairing (1/2:ℝ) v
    (sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num) (C u))=
    sphereSobolevDualPairing (1/2:ℝ) (Ca v)
      (sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num) u)
  rw [half_dual_pairing_inclusion,half_dual_pairing_inclusion]
  exact (real_inner_comm _ _).trans ((hHalf u v).trans (real_inner_comm _ _))
end ShrinkingSpheres
