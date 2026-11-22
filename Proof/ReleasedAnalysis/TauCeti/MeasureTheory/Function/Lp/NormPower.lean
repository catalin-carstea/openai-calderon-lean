/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Proof.ReleasedAnalysis.TauCeti.MeasureTheory.Function.Lp.Norm
import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm

/-! The integral norm-power identity from the Tau Ceti supplement in
arxiv-2610.13592-lean revision 4cfcab036aedbb4f825a3aeb366da12fe5673ddd. -/

public section

open scoped ENNReal

namespace MeasureTheory

/-- For `0 < p < ∞`, the integral of the `p`-th power of the pointwise norm of an `Lᵖ` function
is the `p`-th power of its `Lᵖ` norm. -/
theorem Lp.integral_norm_rpow_eq_norm_rpow {alpha F : Type*} [MeasurableSpace alpha]
    {m : Measure alpha} [NormedAddCommGroup F] {p : ℝ≥0∞} (hp0 : p ≠ 0) (hp : p ≠ ∞)
    (f : Lp F p m) :
    ∫ x, ‖f x‖ ^ p.toReal ∂m = ‖f‖ ^ p.toReal := by
  have h_nonneg : 0 ≤ ∫ x, ‖f x‖ ^ p.toReal ∂m :=
    integral_nonneg fun x => Real.rpow_nonneg (norm_nonneg _) _
  rw [Lp.norm_def, toReal_eLpNorm,
    lpNorm_eq_integral_norm_rpow_toReal hp0 hp (Lp.aestronglyMeasurable f),
    ← Real.rpow_mul h_nonneg, inv_mul_cancel₀ (ENNReal.toReal_pos hp0 hp).ne', Real.rpow_one]

end MeasureTheory
