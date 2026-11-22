module

public import Proof.CalderonPatch.NativeBoundaryMetricChart

import Mathlib.Analysis.Convex.Measure
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

public section

noncomputable section
open Set Metric Filter MeasureTheory
open scoped Topology

namespace CalderonPatch

open CalderonN (X I axis)

variable {n : ℕ}

theorem ae_ball_eq_closedBall (x : X n) {r : ℝ} (hr : 0 < r) :
    ball x r =ᵐ[volume] closedBall x r := by
  have h := measure_eq_zero_iff_ae_notMem.mp ((convex_ball x r).addHaar_frontier volume)
  filter_upwards [h] with y hy
  apply propext
  change y ∈ ball x r ↔ y ∈ closedBall x r
  refine ⟨fun hB => ball_subset_closedBall hB,fun hyC => ?_⟩
  by_contra hyB
  apply hy
  rw [frontier,closure_ball x hr.ne',isOpen_ball.interior_eq]
  exact ⟨hyC,hyB⟩

theorem ae_positiveHalfSpace_eq_inwardHalfSpace [NeZero n] :
    positiveHalfSpace n =ᵐ[volume] inwardHalfSpace n := by
  let A := (EuclideanSpace.proj (𝕜 := ℝ) (0 : I n)).toLinearMap.ker
  have hA : A ≠ ⊤ := by
    intro h
    have hx : axis (0 : I n) ∈ A := h.symm ▸ Submodule.mem_top
    change axis (0 : I n) 0 = 0 at hx
    simp [axis] at hx
  have h := measure_eq_zero_iff_ae_notMem.mp (Measure.addHaar_submodule volume A hA)
  filter_upwards [h] with y hy
  apply propext
  have hy₀ : y 0 ≠ 0 := hy
  exact lt_iff_le_and_ne.trans (and_iff_left (Ne.symm hy₀))

theorem isClosed_inwardHalfSpace [NeZero n] : IsClosed (inwardHalfSpace n) :=
  isClosed_le continuous_const (EuclideanSpace.proj (𝕜 := ℝ) (0 : I n)).continuous

end CalderonPatch
