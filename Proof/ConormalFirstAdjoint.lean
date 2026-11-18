import Proof.FlatDegreeCompatibility
import Proof.CoarseScalarInverse

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1400000
set_option maxSynthPendingDepth 15
open scoped InnerProductSpace
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.SphereHarmonic

theorem boundary_operator_eq_of_inner
    (A B : SphereSobolev 1 →L[ℝ] SphereSobolev 0)
    (h : ∀ u v,⟪A u,sphereSobolevInclusionL 1 0 (by norm_num) v⟫_ℝ =
      ⟪B u,sphereSobolevInclusionL 1 0 (by norm_num) v⟫_ℝ) : A = B := by
  apply ContinuousLinearMap.ext
  intro u
  apply ext_inner_right ℝ
  intro z
  have hEq : (fun v : SphereSobolev 0 => ⟪A u,v⟫_ℝ) = (fun v : SphereSobolev 0 => ⟪B u,v⟫_ℝ) :=
    (denseRange_sphereSobolevInclusionL 1 0 (by norm_num)).equalizer (by fun_prop) (by fun_prop)
      (funext (h u))
  exact congrFun hEq z

/-- Symmetry of the true first conormal form identifies the radial first
    adjoint correction with the Hilbert adjoint of its bounded L2 correction.
    This avoids a derivative bound on an arbitrary angular frame. -/
theorem conormal_first_adjoint_identity
    (N1 : SphereSobolev 1 →L[ℝ] SphereSobolev 0)
    (B M0 : SphereSobolev 0 →L[ℝ] SphereSobolev 0)
    (M1 : SphereSobolev 1 →L[ℝ] SphereSobolev 1) (c : ℝ)
    (hFirst : N1 = c • B.comp (sphereSobolevInclusionL 1 0 (by norm_num))+M0.comp sphereSobolevDegreeL)
    (hM : ∀ u,sphereSobolevInclusionL 1 0 (by norm_num) (M1 u) =
      M0 (sphereSobolevInclusionL 1 0 (by norm_num) u))
    (hM0 : ∀ u v,⟪M0 u,v⟫_ℝ = ⟪u,M0 v⟫_ℝ)
    (hSym : ∀ u v,⟪N1 u,sphereSobolevInclusionL 1 0 (by norm_num) v⟫_ℝ =
      ⟪sphereSobolevInclusionL 1 0 (by norm_num) u,N1 v⟫_ℝ) :
    N1-sphereSobolevDegreeL.comp M1 =
      c • (B.adjoint.comp (sphereSobolevInclusionL 1 0 (by norm_num))) := by
  apply boundary_operator_eq_of_inner
  intro u v
  let I := sphereSobolevInclusionL 1 0 (by norm_num)
  have hLM : ⟪sphereSobolevDegreeL (M1 u),I v⟫_ℝ = ⟪I u,M0 (sphereSobolevDegreeL v)⟫_ℝ :=
    (sphereSobolevDegreeL_symmetric (M1 u) v).trans
      ((congrArg (fun z : SphereSobolev 0 => ⟪z,sphereSobolevDegreeL v⟫_ℝ) (hM u)).trans
        (hM0 (I u) (sphereSobolevDegreeL v)))
  have hFirstV := congrArg (fun A : SphereSobolev 1 →L[ℝ] SphereSobolev 0 => A v) hFirst
  have hPair : ⟪I u,N1 v⟫_ℝ-⟪I u,M0 (sphereSobolevDegreeL v)⟫_ℝ = c*⟪I u,B (I v)⟫_ℝ := by
    have h := congrArg (fun z : SphereSobolev 0 => ⟪I u,z⟫_ℝ-⟪I u,M0 (sphereSobolevDegreeL v)⟫_ℝ) hFirstV
    simpa only [_root_.add_apply,_root_.smul_apply,ContinuousLinearMap.comp_apply,
      inner_add_right,real_inner_smul_right,add_sub_cancel_right] using h
  have hAdj := congrArg (fun t : ℝ => c*t) (ContinuousLinearMap.adjoint_inner_left B (I v) (I u)).symm
  exact (inner_sub_left _ _ _).trans
    ((congrArg₂ (fun x y : ℝ => x-y) (hSym u v) hLM).trans
      (hPair.trans (hAdj.trans (real_inner_smul_left _ _ _).symm)))

theorem conormal_first_adjoint_scaled
    (N1 : SphereSobolev 1 →L[ℝ] SphereSobolev 0)
    (B M0 : SphereSobolev 0 →L[ℝ] SphereSobolev 0)
    (M1 : SphereSobolev 1 →L[ℝ] SphereSobolev 1) (c : ℝ) (hc : c ≠ 0)
    (hFirst : N1 = c • B.comp (sphereSobolevInclusionL 1 0 (by norm_num))+M0.comp sphereSobolevDegreeL)
    (hM : ∀ u,sphereSobolevInclusionL 1 0 (by norm_num) (M1 u) =
      M0 (sphereSobolevInclusionL 1 0 (by norm_num) u))
    (hM0 : ∀ u v,⟪M0 u,v⟫_ℝ = ⟪u,M0 v⟫_ℝ)
    (hSym : ∀ u v,⟪N1 u,sphereSobolevInclusionL 1 0 (by norm_num) v⟫_ℝ =
      ⟪sphereSobolevInclusionL 1 0 (by norm_num) u,N1 v⟫_ℝ) :
    c⁻¹ • (N1-sphereSobolevDegreeL.comp M1) = B.adjoint.comp (sphereSobolevInclusionL 1 0 (by norm_num)) := by
  have h := congrArg (fun T : SphereSobolev 1 →L[ℝ] SphereSobolev 0 => c⁻¹ • T)
    (conormal_first_adjoint_identity N1 B M0 M1 c hFirst hM hM0 hSym)
  exact h.trans (inv_smul_smul₀ hc _)

end ShrinkingSpheres
