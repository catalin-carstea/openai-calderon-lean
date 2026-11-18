import Proof.CompactSupportedMeasurableMajorant
import Mathlib.MeasureTheory.Function.LpSeminorm.SMul

noncomputable section
set_option autoImplicit false
open Set Filter MeasureTheory
open scoped ENNReal
namespace ShrinkingSpheres

lemma memLp_local_scalar_smul_of_compact_support
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {Y S : Set X} (hY : MeasurableSet Y) (hS : IsCompact S) (hSY : S ⊆ Y)
    (f : X → E) {p : ℝ≥0∞} (hf : MemLp f p (volume.restrict Y))
    (h0 : ∀ y ∈ Y,y ∉ S → f y=0) (c : X → ℝ) (hc : ContinuousOn c Y) :
    MemLp (fun y => c y • f y) p (volume.restrict Y) := by
  obtain ⟨C,hC⟩ := hS.exists_bound_of_continuousOn (hc.mono hSY)
  apply (hf.norm.const_mul |C|).mono'
    ((hc.aestronglyMeasurable (μ:=volume) hY).smul hf.aestronglyMeasurable)
  filter_upwards [ae_restrict_mem hY] with y hy
  change ‖c y • f y‖ ≤ |C| * ‖f y‖
  by_cases hs : y ∈ S
  · rw [norm_smul]
    exact mul_le_mul_of_nonneg_right ((hC y hs).trans (le_abs_self C)) (norm_nonneg _)
  · rw [h0 y hy hs,smul_zero,norm_zero,mul_zero]

end ShrinkingSpheres
