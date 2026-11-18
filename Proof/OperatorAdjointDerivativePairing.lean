import Proof.FirstAdjointNormalForm
import Mathlib.Analysis.InnerProductSpace.Calculus

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter
open scoped ContDiff Topology InnerProductSpace
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.SphereHarmonic

/-- Differentiating an actual same-family adjoint pairing gives the true
    pairing for the two operator derivatives on their common H1 domain. -/
theorem operator_derivative_adjoint_pairing
    (A B : ℝ → SphereSobolev 1 →L[ℝ] SphereSobolev 0)
    (DA DB : SphereSobolev 1 →L[ℝ] SphereSobolev 0)
    (hA : HasDerivAt A DA 0) (hB : HasDerivAt B DB 0)
    (hPair : ∀ᶠ t : ℝ in 𝓝 0,∀ u v : SphereSobolev 1,
      ⟪A t u,sphereSobolevInclusionL 1 0 (by norm_num) v⟫_ℝ =
        ⟪sphereSobolevInclusionL 1 0 (by norm_num) u,B t v⟫_ℝ) :
    ∀ u v : SphereSobolev 1,⟪DA u,sphereSobolevInclusionL 1 0 (by norm_num) v⟫_ℝ =
      ⟪sphereSobolevInclusionL 1 0 (by norm_num) u,DB v⟫_ℝ := by
  intro u v
  have ha := (hA.clm_apply (hasDerivAt_const (0:ℝ) u)).inner ℝ
    (hasDerivAt_const (0:ℝ) (sphereSobolevInclusionL 1 0 (by norm_num) v))
  have hb := (hasDerivAt_const (0:ℝ) (sphereSobolevInclusionL 1 0 (by norm_num) u)).inner ℝ
    (hB.clm_apply (hasDerivAt_const (0:ℝ) v))
  have hEq : (fun t : ℝ => ⟪A t u,sphereSobolevInclusionL 1 0 (by norm_num) v⟫_ℝ) =ᶠ[𝓝 0]
      (fun t => ⟪sphereSobolevInclusionL 1 0 (by norm_num) u,B t v⟫_ℝ) :=
    hPair.mono (fun t ht => ht u v)
  have hh := ha.unique (hb.congr_of_eventuallyEq hEq)
  simpa only [zero_apply,map_zero,add_zero,zero_add,inner_zero_left,inner_zero_right] using hh

end ShrinkingSpheres
