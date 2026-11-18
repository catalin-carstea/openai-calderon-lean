import Proof.CompactSupportedLpLocalScalar
import Mathlib.MeasureTheory.Function.L2Space

noncomputable section
set_option autoImplicit false
open Set Filter MeasureTheory
open scoped ENNReal
namespace ShrinkingSpheres

lemma integrableOn_local_weighted_norm_sq_of_memLp
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {Y S : Set X} (hY : MeasurableSet Y) (hS : IsCompact S) (hSY : S ⊆ Y)
    (f : X → E) (hf : MemLp f 2 (volume.restrict Y))
    (h0 : ∀ y ∈ Y,y ∉ S → f y=0) (c : X → ℝ) (hc : ContinuousOn c Y)
    (hc0 : ∀ y ∈ Y,0 ≤ c y) : IntegrableOn (fun y => c y*‖f y‖^2) Y := by
  have hLp := memLp_local_scalar_smul_of_compact_support hY hS hSY f hf h0
    (fun y => Real.sqrt (c y)) hc.sqrt
  have hI := (memLp_two_iff_integrable_sq_norm hLp.aestronglyMeasurable).1 hLp
  apply hI.congr
  filter_upwards [ae_restrict_mem hY] with y hy
  simp only [norm_smul,Real.norm_eq_abs,mul_pow,sq_abs,Real.sq_sqrt (hc0 y hy)]

lemma integrableOn_local_weighted_inner_of_memLp
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {Y S : Set X} (hY : MeasurableSet Y) (hS : IsCompact S) (hSY : S ⊆ Y)
    (f g : X → E) (hf : MemLp f 2 (volume.restrict Y)) (hg : MemLp g 2 (volume.restrict Y))
    (h0 : ∀ y ∈ Y,y ∉ S → f y=0) (c : X → ℝ) (hc : ContinuousOn c Y) :
    IntegrableOn (fun y => c y*inner ℝ (f y) (g y)) Y := by
  have hcf := memLp_local_scalar_smul_of_compact_support hY hS hSY f hf h0 c hc
  have hDom := hcf.norm.integrable_mul hg.norm
  have hInner : Integrable (fun y => inner ℝ (c y • f y) (g y)) (volume.restrict Y) := by
    apply hDom.mono' (hcf.aestronglyMeasurable.inner hg.aestronglyMeasurable)
    exact Eventually.of_forall (fun y => norm_inner_le_norm (c y • f y) (g y))
  change Integrable (fun y => c y*inner ℝ (f y) (g y)) (volume.restrict Y)
  simpa only [real_inner_smul_left] using hInner

end ShrinkingSpheres
