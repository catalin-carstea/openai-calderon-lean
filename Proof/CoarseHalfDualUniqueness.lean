import Proof.CoarseHalfDualCompletion

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000
open Set
open scoped InnerProductSpace
namespace OAI.AnisotropicCalderon.SphereHarmonic

/-- Both dense inclusions determine the completed half-order operator. -/
lemma half_operator_eq_of_coarse_dual_pairs
    (S T : SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ)))
    (hPair : ∀ u : SphereSobolev 2,∀ v : SphereSobolev 1,
      sphereSobolevDualPairing (1/2:ℝ) (sphereSobolevInclusionL 1 (1/2:ℝ) (by norm_num) v)
        (S (sphereSobolevInclusionL 2 (1/2:ℝ) (by norm_num) u)) =
      sphereSobolevDualPairing (1/2:ℝ) (sphereSobolevInclusionL 1 (1/2:ℝ) (by norm_num) v)
        (T (sphereSobolevInclusionL 2 (1/2:ℝ) (by norm_num) u))) : S = T := by
  let I := sphereSobolevInclusionL 2 (1/2:ℝ) (by norm_num)
  let J := sphereSobolevInclusionL 1 (1/2:ℝ) (by norm_num)
  have hEq (u : SphereSobolev 2) : S (I u) = T (I u) := by
    have hh :
        (fun v : SphereSobolev (1/2:ℝ) => sphereSobolevDualPairing (1/2:ℝ) v (S (I u))) =
        (fun v : SphereSobolev (1/2:ℝ) => sphereSobolevDualPairing (1/2:ℝ) v (T (I u))) :=
      (denseRange_sphereSobolevInclusionL 1 (1/2:ℝ) (by norm_num)).equalizer
      (continuous_id.inner continuous_const) (continuous_id.inner continuous_const) (funext (hPair u))
    apply ext_inner_left ℝ
    intro v
    exact congr_fun hh v
  have hh := (denseRange_sphereSobolevInclusionL 2 (1/2:ℝ) (by norm_num)).equalizer
    S.continuous T.continuous (funext hEq)
  exact ContinuousLinearMap.ext (fun u => congr_fun hh u)

end OAI.AnisotropicCalderon.SphereHarmonic
