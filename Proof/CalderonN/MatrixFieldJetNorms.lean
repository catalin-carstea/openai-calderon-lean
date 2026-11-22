module

public import Proof.CalderonN.Chart
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Matrix.Normed
import Mathlib.Tactic
import Mathlib.Analysis.Calculus.ContDiff.Bounds

/-! Adapted from the checked Proposition 5.3 release. -/

public section

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1400000
set_option maxSynthPendingDepth 20
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Filter
open scoped ContDiff Topology Matrix.Norms.Elementwise
namespace CalderonN

variable {dim : ℕ}

@[expose] def matrixEntryL (k l : (I dim)) : (Mat dim) →L[ℝ] ℝ :=
  ({toFun := fun A : (Mat dim) => A k l
    map_add' := by intros; rfl
    map_smul' := by intros; rfl} : (Mat dim) →ₗ[ℝ] ℝ).mkContinuous 1
      (fun A => by
        change ‖A k l‖ ≤ 1*‖A‖
        simpa only [one_mul] using Matrix.norm_entry_le_entrywise_sup_norm A (i:=k) (j:=l))

lemma matrixEntryL_apply (k l : (I dim)) (A : (Mat dim)) : matrixEntryL k l A = A k l := rfl

lemma fderiv_matrix_entry (a : (X dim) → (Mat dim)) (z : (X dim)) (ha : DifferentiableAt ℝ a z) (k l : (I dim)) :
    fderiv ℝ (fun w => a w k l) z = (matrixEntryL k l).comp (fderiv ℝ a z) := by
  simpa only [Function.comp_def,matrixEntryL_apply] using
    ((matrixEntryL k l).hasFDerivAt.comp z ha.hasFDerivAt).fderiv

lemma norm_fderiv_matrix_le_of_entries (a : (X dim) → (Mat dim)) (z : (X dim)) (ha : DifferentiableAt ℝ a z)
    (C : ℝ) (hC : 0 ≤ C) (h : ∀ k l,‖fderiv ℝ (fun w => a w k l) z‖ ≤ C) :
    ‖fderiv ℝ a z‖ ≤ C := by
  apply ContinuousLinearMap.opNorm_le_bound _ hC
  intro b
  apply (Matrix.norm_le_iff (mul_nonneg hC (norm_nonneg b))).mpr
  intro k l
  have hEq : fderiv ℝ (fun w => a w k l) z b = fderiv ℝ a z b k l :=
    congrArg (fun T : (X dim) →L[ℝ] ℝ => T b) (fderiv_matrix_entry a z ha k l)
  change ‖fderiv ℝ a z b k l‖ ≤ _
  rw [← hEq]
  exact ((fderiv ℝ (fun w => a w k l) z).le_opNorm b).trans
    (mul_le_mul_of_nonneg_right (h k l) (norm_nonneg b))

lemma second_fderiv_matrix_entry (a : (X dim) → (Mat dim)) (z : (X dim)) (ha : ContDiffAt ℝ ∞ a z)
    (k l : (I dim)) (b c : (X dim)) :
    fderiv ℝ (fderiv ℝ (fun w => a w k l)) z b c = fderiv ℝ (fderiv ℝ a) z b c k l := by
  have hNear : ∀ᶠ w in 𝓝 z,DifferentiableAt ℝ a w := by
    filter_upwards [(ha.of_le (by simp : (2:WithTop ℕ∞) ≤ ∞)).eventually (by norm_num)] with w hw
    exact hw.differentiableAt (by norm_num)
  have hEq : (fun w => fderiv ℝ (fun q => a q k l) w) =ᶠ[𝓝 z]
      (fun w => (matrixEntryL k l).comp (fderiv ℝ a w)) := by
    filter_upwards [hNear] with w hw
    exact fderiv_matrix_entry a w hw k l
  let Post : ((X dim) →L[ℝ] (Mat dim)) →L[ℝ] ((X dim) →L[ℝ] ℝ) :=
    (ContinuousLinearMap.compL ℝ (X dim) (Mat dim) ℝ) (matrixEntryL k l)
  have hDa : DifferentiableAt ℝ (fderiv ℝ a) z :=
    (ha.fderiv_right (m:=1) (by simp)).differentiableAt (by norm_num)
  have hPost := Post.hasFDerivAt.comp z hDa.hasFDerivAt
  have hD : fderiv ℝ (fun w => fderiv ℝ (fun q => a q k l) w) z =
      Post.comp (fderiv ℝ (fderiv ℝ a) z) := hEq.fderiv_eq.trans hPost.fderiv
  simpa only [Post,ContinuousLinearMap.comp_apply,ContinuousLinearMap.compL_apply,matrixEntryL_apply] using
    congrArg (fun T : (X dim) →L[ℝ] (X dim) →L[ℝ] ℝ => T b c) hD

lemma norm_second_fderiv_matrix_le_of_entries (a : (X dim) → (Mat dim)) (z : (X dim)) (ha : ContDiffAt ℝ ∞ a z)
    (C : ℝ) (hC : 0 ≤ C)
    (h : ∀ k l,‖fderiv ℝ (fderiv ℝ (fun w => a w k l)) z‖ ≤ C) :
    ‖fderiv ℝ (fderiv ℝ a) z‖ ≤ C := by
  apply ContinuousLinearMap.opNorm_le_bound _ hC
  intro b
  apply ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg hC (norm_nonneg b))
  intro c
  apply (Matrix.norm_le_iff (mul_nonneg (mul_nonneg hC (norm_nonneg b)) (norm_nonneg c))).mpr
  intro k l
  change ‖fderiv ℝ (fderiv ℝ a) z b c k l‖ ≤ _
  rw [← second_fderiv_matrix_entry a z ha k l b c]
  exact (ContinuousLinearMap.le_opNorm₂ _ b c).trans
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (h k l) (norm_nonneg b)) (norm_nonneg c))

end CalderonN
