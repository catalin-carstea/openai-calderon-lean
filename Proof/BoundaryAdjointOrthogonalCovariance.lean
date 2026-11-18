import Proof.NormalFrameRadialRotationCovariance
import Proof.ConormalFirstAdjoint

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxSynthPendingDepth 25
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set
open scoped InnerProductSpace
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.EnergyBridge OAI.AnisotropicCalderon.DirichletFamily
open OAI.AnisotropicCalderon.SphereHarmonic
attribute [local irreducible] sphereSobolevDegreeL

lemma sphereSobolevDegreeL_orthogonal_covariance (e : X ≃ₗᵢ[ℝ] X) :
    sphereSobolevDegreeL.comp (sphereSobolevOrthogonalPullbackL 1 e) =
      (sphereSobolevOrthogonalPullbackL 0 e).comp sphereSobolevDegreeL := by
  apply sphereSobolev_clm_eq_of_single 1
  intro k a
  change sphereSobolevDegreeL (sphereSobolevOrthogonalPullbackL 1 e (sphereSobolevSingleL 1 k a)) =
    sphereSobolevOrthogonalPullbackL 0 e (sphereSobolevDegreeL (sphereSobolevSingleL 1 k a))
  rw [sphereSobolevOrthogonalPullbackL_single,sphereSobolevDegreeL_single,sphereSobolevDegreeL_single,map_smul,
    sphereSobolevOrthogonalPullbackL_single]

/-- True L2 adjunction and forward orthogonal covariance determine the
orthogonal covariance of the actual H1-to-L2 adjoints by dense testing. -/
theorem boundary_adjoint_orthogonal_covariance (e : X ≃ₗᵢ[ℝ] X)
    (D0 Dθ Da0 Daθ : SphereSobolev 1 →L[ℝ] SphereSobolev 0)
    (hAdj0 : ∀ u v,⟪D0 u,sphereSobolevInclusionL 1 0 (by norm_num) v⟫_ℝ =
      ⟪sphereSobolevInclusionL 1 0 (by norm_num) u,Da0 v⟫_ℝ)
    (hAdjθ : ∀ u v,⟪Dθ u,sphereSobolevInclusionL 1 0 (by norm_num) v⟫_ℝ =
      ⟪sphereSobolevInclusionL 1 0 (by norm_num) u,Daθ v⟫_ℝ)
    (hCov : ∀ u,Dθ (sphereSobolevOrthogonalPullbackL 1 e u) = sphereSobolevOrthogonalPullbackL 0 e (D0 u)) :
    Daθ.comp (sphereSobolevOrthogonalPullbackL 1 e) =
      (sphereSobolevOrthogonalPullbackL 0 e).comp Da0 := by
  let I0 := sphereSobolevInclusionL 1 0 (by norm_num)
  let P0 := sphereSobolevOrthogonalPullbackL 0 e
  let P1 := sphereSobolevOrthogonalPullbackL 1 e
  have hI (u : SphereSobolev 1) : I0 (P1 u) = P0 (I0 u) :=
    congrArg (fun T : SphereSobolev 1 →L[ℝ] SphereSobolev 0 => T u)
      (sphereSobolevInclusionL_orthogonalPullback 1 0 (by norm_num) e)
  have hInner (u v : SphereSobolev 0) : ⟪P0 u,P0 v⟫_ℝ = ⟪u,v⟫_ℝ :=
    (sphereSobolevOrthogonalPullback 0 e).inner_map_map u v
  apply boundary_operator_eq_of_inner
  intro u v
  let v' := sphereSobolevOrthogonalPullbackL 1 e.symm v
  have hv : P1 v' = v := sphereSobolevOrthogonalPullbackL_symm_apply 1 e.symm v
  have hvI : I0 v = P0 (I0 v') := (congrArg I0 hv).symm.trans (hI v')
  change ⟪Daθ (P1 u),I0 v⟫_ℝ = ⟪P0 (Da0 u),I0 v⟫_ℝ
  calc
    _ = ⟪P0 (I0 v'),Daθ (P1 u)⟫_ℝ := by rw [hvI,real_inner_comm]
    _ = ⟪Dθ (P1 v'),I0 (P1 u)⟫_ℝ := by
      have hh := hAdjθ (P1 v') (P1 u)
      change ⟪Dθ (P1 v'),I0 (P1 u)⟫_ℝ = ⟪I0 (P1 v'),Daθ (P1 u)⟫_ℝ at hh
      exact (congrArg (fun z : SphereSobolev 0 => ⟪z,Daθ (P1 u)⟫_ℝ) (hI v').symm).trans hh.symm
    _ = ⟪P0 (D0 v'),P0 (I0 u)⟫_ℝ := congrArg₂ (fun a b : SphereSobolev 0 => ⟪a,b⟫_ℝ) (hCov v') (hI u)
    _ = ⟪D0 v',I0 u⟫_ℝ := hInner _ _
    _ = ⟪I0 v',Da0 u⟫_ℝ := hAdj0 v' u
    _ = ⟪P0 (I0 v'),P0 (Da0 u)⟫_ℝ := (hInner _ _).symm
    _ = _ := by rw [← hvI,real_inner_comm]

end ShrinkingSpheres
