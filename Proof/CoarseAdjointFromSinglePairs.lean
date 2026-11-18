import Proof.SphereSobolevOperatorExt
import Proof.PhysicalHarmonicBlockCasimir
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set
open scoped InnerProductSpace
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.SphereHarmonic

lemma coarsePhysicalHarmonicBlock_sobolev_pairing
    (R : SphereSobolev 1 →L[ℝ] SphereSobolev 0)
    (m n : ℕ) (z : harmonicSphereSubspace n) (w : harmonicSphereSubspace m) :
    ⟪coarsePhysicalHarmonicBlock R m n z,w⟫_ℝ =
      ⟪R (sphereSobolevSingleL 1 n z),
        sphereSobolevInclusionL 1 0 (by norm_num) (sphereSobolevSingleL 1 m w)⟫_ℝ := by
  have hh := sphereSobolevDualPairing_single_left_physical 0 m w (R (sphereSobolevSingleL 1 n z))
  rw [sphereSobolevInclusionL_single]
  simpa only [sphereSobolevCoefficientL,neg_zero,coarsePhysicalHarmonicBlock,ContinuousLinearMap.comp_apply] using hh.symm.trans (real_inner_comm _ _)

/-- True pairings on physical harmonic modes extend to the full H1 domain. -/
lemma coarse_operator_adjoint_pairing_of_singles
    (R Ra : SphereSobolev 1 →L[ℝ] SphereSobolev 0)
    (hSingle : ∀ m n : ℕ,∀ z : harmonicSphereSubspace n,∀ w : harmonicSphereSubspace m,
      ⟪R (sphereSobolevSingleL 1 n z),
        sphereSobolevInclusionL 1 0 (by norm_num) (sphereSobolevSingleL 1 m w)⟫_ℝ =
      ⟪sphereSobolevInclusionL 1 0 (by norm_num) (sphereSobolevSingleL 1 n z),
        Ra (sphereSobolevSingleL 1 m w)⟫_ℝ) :
    ∀ u v : SphereSobolev 1,
      ⟪R u,sphereSobolevInclusionL 1 0 (by norm_num) v⟫_ℝ =
        ⟪sphereSobolevInclusionL 1 0 (by norm_num) u,Ra v⟫_ℝ := by
  let I0 := sphereSobolevInclusionL 1 0 (by norm_num)
  have hFirst (n : ℕ) (z : harmonicSphereSubspace n) (v : SphereSobolev 1) :
      ⟪R (sphereSobolevSingleL 1 n z),I0 v⟫_ℝ =
        ⟪I0 (sphereSobolevSingleL 1 n z),Ra v⟫_ℝ := by
    let F := (innerSL ℝ (R (sphereSobolevSingleL 1 n z))).comp I0
    let G := (innerSL ℝ (I0 (sphereSobolevSingleL 1 n z))).comp Ra
    have hFG : F = G := sphereSobolev_clm_ext_on_single 1 F G (fun m w => hSingle m n z w)
    exact congrArg (fun A : SphereSobolev 1 →L[ℝ] ℝ => A v) hFG
  intro u v
  let F := (innerSL ℝ (I0 v)).comp R
  let G := (innerSL ℝ (Ra v)).comp I0
  have hFG : F = G := sphereSobolev_clm_ext_on_single 1 F G (by
    intro n z
    exact (real_inner_comm _ _).trans ((hFirst n z v).trans (real_inner_comm _ _)))
  have hh := congrArg (fun A : SphereSobolev 1 →L[ℝ] ℝ => A u) hFG
  change ⟪I0 v,R u⟫_ℝ = ⟪Ra v,I0 u⟫_ℝ at hh
  exact (real_inner_comm _ _).trans (hh.trans (real_inner_comm (I0 u) (Ra v)))

end ShrinkingSpheres
