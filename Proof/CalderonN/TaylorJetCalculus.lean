module

public import Mathlib.Analysis.Calculus.ContDiff.Operations

public section

noncomputable section
open Set
open scoped ContDiff

namespace CalderonN

/-- With a unique derivative on the domain, every finite jet of an indefinitely
smooth function is indefinitely smooth up to the same boundary. -/
theorem contDiffOn_iteratedFDerivWithin_top {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : E → F} {D : Set E} (hf : ContDiffOn ℝ ∞ f D) (hD : UniqueDiffOn ℝ D)
    (k : ℕ) : ContDiffOn ℝ ∞ (iteratedFDerivWithin ℝ k f D) D := by
  induction k with
  | zero =>
    rw [iteratedFDerivWithin_zero_eq_comp]
    exact (continuousMultilinearCurryFin0 ℝ E F).symm.contDiff.comp_contDiffOn hf
  | succ k ih =>
    rw [iteratedFDerivWithin_succ_eq_comp_left]
    exact (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (k+1) => E) F).symm.contDiff.comp_contDiffOn
      (ih.fderivWithin (m := ∞) hD (by simp))

theorem contDiffOn_iteratedFDeriv_top {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : E → F} {D : Set E} (hf : ContDiffOn ℝ ∞ f D) (hD : IsOpen D)
    (k : ℕ) : ContDiffOn ℝ ∞ (iteratedFDeriv ℝ k f) D :=
  (contDiffOn_iteratedFDerivWithin_top hf hD.uniqueDiffOn k).congr
    (fun _ hx => (iteratedFDerivWithin_of_isOpen k hD hx).symm)

end CalderonN
