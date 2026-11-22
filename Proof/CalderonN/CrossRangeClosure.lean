module

public import Proof.CalderonN.CrossSeriesAgreement

import Mathlib.Analysis.InnerProductSpace.Projection.Submodule
import Mathlib.MeasureTheory.Measure.SeparableMeasure

public section

open Set Filter MeasureTheory TopologicalSpace
open scoped ENNReal

namespace LocalMetricExtension

/-- If every coefficient orthogonal to a restriction range vanishes, almost
every slice is in the closed range. A countable dense family of tests gives
one common full-measure set of slices. -/
theorem ae_slice_mem_rangeClosure
    {α β E : Type*} [MeasurableSpace α] [MeasurableSpace β] [NormedAddCommGroup E] [NormedSpace ℝ E]
    {m : Measure α} {n : Measure β} [SFinite m] [IsFiniteMeasure n]
    [SecondCountableTopology (Lp ℝ 2 m)]
    (R : E →L[ℝ] Lp ℝ 2 m) (q : Lp ℝ 2 (m.prod n))
    (hzero : ∀ z ∈ (LinearMap.range R.toLinearMap)ᗮ, tensorCoefficient z q = 0) :
    ∀ᵐ y ∂n, ∃ u ∈ closure (range R), (u : α → ℝ) =ᵐ[m] fun x => q (x,y) := by
  let V := LinearMap.range R.toLinearMap
  obtain ⟨z, hz⟩ := exists_dense_seq (α := Vᗮ)
  have htest (k : ℕ) : ∀ᵐ y ∂n, (∫ x, (z k : Lp ℝ 2 m) x * q (x,y) ∂m) = 0 := by
    have heq := tensorCoefficient_ae_integral (z k : Lp ℝ 2 m) q
    rw [hzero (z k) (z k).2] at heq
    filter_upwards [heq, Lp.coeFn_zero (E := ℝ) (p := 2) (μ := n)] with y hy hz'
    exact hy.symm.trans hz'
  filter_upwards [ae_all_iff.mpr htest, ae_memLp_left_of_prod q] with y hy hmem
  let u := hmem.toLp (fun x => q (x,y))
  refine ⟨u, ?_, hmem.coeFn_toLp⟩
  change u ∈ V.topologicalClosure
  rw [← Submodule.orthogonal_orthogonal_eq_closure]
  apply (Submodule.mem_orthogonal _ _).mpr
  intro w hw
  let L : Vᗮ →L[ℝ] ℝ := (innerSL ℝ u).comp (Vᗮ).subtypeL
  have hL (k : ℕ) : L (z k) = 0 := by
    change inner ℝ u (z k : Lp ℝ 2 m) = 0
    rw [L2.inner_def]
    refine (integral_congr_ae ?_).trans (hy k)
    filter_upwards [hmem.coeFn_toLp] with x hx
    rw [RCLike.inner_apply, conj_trivial, hx]
  have hker : closure (range z) ⊆ L.ker :=
    closure_minimal (by rintro _ ⟨k, rfl⟩; exact hL k) L.isClosed_ker
  have hLw : L ⟨w, hw⟩ = 0 :=
    hker (hz ⟨w, hw⟩)
  change inner ℝ u w = 0 at hLw
  exact (real_inner_comm u w).trans hLw

end LocalMetricExtension
