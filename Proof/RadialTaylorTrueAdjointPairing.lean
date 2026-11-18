import Proof.FirstAdjointNormalForm
import Proof.FlatDegreeCompatibility

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

/-- Subtracting the same flat and true first-adjoint terms preserves the
    actual probability-sphere adjunction for the quadratic remainders. -/
theorem radial_taylor_true_adjoint_pairing
    (R Da : SphereSobolev 1 →L[ℝ] SphereSobolev 0)
    (B : SphereSobolev 0 →L[ℝ] SphereSobolev 0) (r : ℝ)
    (hPair : ∀ u v : SphereSobolev 1,
      ⟪(R+sphereSobolevDegreeL) u,sphereSobolevInclusionL 1 0 (by norm_num) v⟫_ℝ =
        ⟪sphereSobolevInclusionL 1 0 (by norm_num) u,Da v⟫_ℝ) :
    ∀ u v : SphereSobolev 1,
      ⟪(R-r • B.comp (sphereSobolevInclusionL 1 0 (by norm_num))) u,
        sphereSobolevInclusionL 1 0 (by norm_num) v⟫_ℝ =
      ⟪sphereSobolevInclusionL 1 0 (by norm_num) u,
        radialAdjointTaylorRemainderL Da B r v⟫_ℝ := by
  intro u v
  have hFull := hPair u v
  simp only [_root_.add_apply,inner_add_left] at hFull
  have hDegree := sphereSobolevDegreeL_symmetric u v
  change ⟪R u-r • B (sphereSobolevInclusionL 1 0 (by norm_num) u),
      sphereSobolevInclusionL 1 0 (by norm_num) v⟫_ℝ =
    ⟪sphereSobolevInclusionL 1 0 (by norm_num) u,Da v-sphereSobolevDegreeL v-
      r • B.adjoint (sphereSobolevInclusionL 1 0 (by norm_num) v)⟫_ℝ
  simp only [inner_sub_left,inner_sub_right,real_inner_smul_left,inner_smul_right]
  rw [B.adjoint_inner_right]
  linarith only [hFull,hDegree]

end ShrinkingSpheres
