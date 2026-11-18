import Proof.SupportedOperatorCalculus
import Proof.Geometry
import Mathlib.MeasureTheory.Function.LpSeminorm.Indicator

noncomputable section
set_option autoImplicit false
open Set Filter MeasureTheory
open scoped ENNReal
namespace ShrinkingSpheres

/-- Local continuous domination on the actual compact support gives every
finite (and infinite) base Lp domain, without asserting continuity of the
measurable section itself. -/
lemma memLp_of_compact_supported_continuousOn_majorant
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {Y S : Set X} (hY : MeasurableSet Y) (hS : IsCompact S) (hSY : S ⊆ Y)
    (f : X → E) (hf : AEStronglyMeasurable f (volume.restrict Y))
    (h0 : ∀ y ∈ Y,y ∉ S → f y=0) (B : X → ℝ) (hB : ContinuousOn B Y)
    (hNorm : ∀ y ∈ Y,‖f y‖ ≤ B y) (p : ℝ≥0∞) : MemLp f p (volume.restrict Y) := by
  obtain ⟨C,hC⟩ := hS.exists_bound_of_continuousOn (hB.mono hSY)
  have hInd : MemLp (S.indicator (fun _ : X => |C|)) p volume :=
    memLp_indicator_const p hS.measurableSet.nullMeasurableSet |C| (Or.inr hS.measure_ne_top)
  have hIndY : MemLp (S.indicator (fun _ : X => |C|)) p (volume.restrict Y) :=
    MemLp.mono_measure Measure.restrict_le_self hInd
  apply hIndY.mono' hf
  filter_upwards [ae_restrict_mem hY] with y hy
  by_cases hs : y ∈ S
  · rw [Set.indicator_of_mem hs]
    have hBN : B y ≤ ‖B y‖ := by simpa only [Real.norm_eq_abs] using le_abs_self (B y)
    exact (hNorm y hy).trans (hBN.trans ((hC y hs).trans (le_abs_self C)))
  · rw [Set.indicator_of_notMem hs,h0 y hy hs,norm_zero]

end ShrinkingSpheres
