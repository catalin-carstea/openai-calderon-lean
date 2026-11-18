import Proof.MatrixFieldJetNorms
import Proof.BackgroundBudgets

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter
open scoped ContDiff Topology Matrix.Norms.Elementwise
namespace ShrinkingSpheres

/-- The canonical entrywise matrix norm preserves the common coordinate
jet budget at every finite order. No dimension loss is needed. -/
lemma norm_iteratedFDeriv_matrix_le_of_entries {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    (G : P → Mat) (p : P) (hG : ContDiffAt ℝ ∞ G p) (n : ℕ) (C : ℝ) (hC : 0 ≤ C)
    (hEntries : ∀ i j,‖iteratedFDeriv ℝ n (fun q => G q i j) p‖ ≤ C) :
    ‖iteratedFDeriv ℝ n G p‖ ≤ C := by
  apply ContinuousMultilinearMap.opNorm_le_bound hC
  intro v
  apply (Matrix.norm_le_iff (mul_nonneg hC (Finset.prod_nonneg (fun _ _ => norm_nonneg _)))).mpr
  intro i j
  have hComp := (matrixEntryL i j).iteratedFDeriv_comp_left hG (i:=n) (by simp)
  have hEval := congrArg (fun L : ContinuousMultilinearMap ℝ (fun _ : Fin n => P) ℝ => L v) hComp
  have hEq : iteratedFDeriv ℝ n (fun q => G q i j) p v = iteratedFDeriv ℝ n G p v i j := by
    change iteratedFDeriv ℝ n ((matrixEntryL i j) ∘ G) p v = matrixEntryL i j (iteratedFDeriv ℝ n G p v) at hEval
    simpa only [Function.comp_def,matrixEntryL_apply] using hEval
  change ‖iteratedFDeriv ℝ n G p v i j‖ ≤ _
  rw [← hEq]
  exact ((iteratedFDeriv ℝ n (fun q => G q i j) p).le_opNorm v).trans
    (mul_le_mul_of_nonneg_right (hEntries i j) (Finset.prod_nonneg (fun _ _ => norm_nonneg _)))

lemma Background.reference_matrix_jet_bound {Ω : Set X} (hΩ : IsOpen Ω) {K : ℝ} {m : ℕ}
    {M : Fin (m+1) → ℝ} {g g₁ g₂ : MetricField} {e : Frame}
    (h : Background Ω K M g g₁ g₂ e) (j : Fin (m+1)) {y : X} (hy : y ∈ Ω) :
    ‖iteratedFDeriv ℝ j.val g y‖ ≤ |M j| := by
  have hSmooth : ContDiffAt ℝ ∞ g y :=
    contDiffAt_pi.mpr (fun i => contDiffAt_pi.mpr (fun k => (h.1.1 i k).contDiffAt (hΩ.mem_nhds hy)))
  exact norm_iteratedFDeriv_matrix_le_of_entries g y hSmooth j.val |M j| (abs_nonneg _)
    (fun i k => (h.reference_jet_bound j hy i k).trans (le_abs_self _))

end ShrinkingSpheres
