import Proof.MatrixFieldJetNorms

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1400000
set_option maxSynthPendingDepth 20
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter
open scoped ContDiff Topology Matrix.Norms.Elementwise
namespace ShrinkingSpheres

def affineMatrixRemainder (a : X → Mat) (c r : ℝ) (ell : X →L[ℝ] ℝ) (z : X) : Mat :=
  a z-(c+r*ell z) • (1:Mat)

lemma affineMatrixRemainder_entry (a : X → Mat) (c r : ℝ) (ell : X →L[ℝ] ℝ) (z : X) (k l : I) :
    affineMatrixRemainder a c r ell z k l = a z k l-(c+r*ell z)*(1:Mat) k l := rfl

lemma fderiv_affine_scalar_entry (c r t : ℝ) (ell : X →L[ℝ] ℝ) (z : X) :
    fderiv ℝ (fun w => (c+r*ell w)*t) z = (r*t) • ell := by
  have hFun : (fun w => (c+r*ell w)*t) = (fun w => c*t+((r*t) • ell) w) := by
    funext w
    simp only [_root_.smul_apply,smul_eq_mul]
    ring
  rw [hFun,fderiv_const_add,ContinuousLinearMap.fderiv]

lemma fderiv_affineMatrixRemainder_entry (a : X → Mat) (c r : ℝ) (ell : X →L[ℝ] ℝ)
    (z : X) (ha : DifferentiableAt ℝ a z) (k l : I) :
    fderiv ℝ (fun w => affineMatrixRemainder a c r ell w k l) z =
      fderiv ℝ (fun w => a w k l) z-(r*(1:Mat) k l) • ell := by
  have hEntry : DifferentiableAt ℝ (fun w => a w k l) z :=
    ((matrixEntryL k l).differentiableAt.comp z ha)
  have hAffine : DifferentiableAt ℝ (fun w => (c+r*ell w)*(1:Mat) k l) z := by fun_prop
  change fderiv ℝ ((fun w => a w k l)-(fun w => (c+r*ell w)*(1:Mat) k l)) z = _
  rw [fderiv_sub hEntry hAffine,fderiv_affine_scalar_entry]

lemma second_fderiv_affineMatrixRemainder_entry (a : X → Mat) (c r : ℝ) (ell : X →L[ℝ] ℝ)
    (z : X) (ha : ContDiffAt ℝ ∞ a z) (k l : I) :
    fderiv ℝ (fderiv ℝ (fun w => affineMatrixRemainder a c r ell w k l)) z =
      fderiv ℝ (fderiv ℝ (fun w => a w k l)) z := by
  have hNear : ∀ᶠ w in 𝓝 z,DifferentiableAt ℝ a w := by
    filter_upwards [(ha.of_le (by simp : (2:WithTop ℕ∞) ≤ ∞)).eventually (by norm_num)] with w hw
    exact hw.differentiableAt (by norm_num)
  have hEq : (fun w => fderiv ℝ (fun q => affineMatrixRemainder a c r ell q k l) w) =ᶠ[𝓝 z]
      (fun w => fderiv ℝ (fun q => a q k l) w-(r*(1:Mat) k l) • ell) := by
    filter_upwards [hNear] with w hw
    exact fderiv_affineMatrixRemainder_entry a c r ell w hw k l
  exact hEq.fderiv_eq.trans (fderiv_sub_const _)

lemma contDiffAt_affineMatrixRemainder (a : X → Mat) (c r : ℝ) (ell : X →L[ℝ] ℝ)
    (z : X) (ha : ContDiffAt ℝ ∞ a z) : ContDiffAt ℝ ∞ (affineMatrixRemainder a c r ell) z :=
  ha.sub ((contDiffAt_const.add (contDiffAt_const.mul ell.contDiff.contDiffAt)).smul contDiffAt_const)

end ShrinkingSpheres
