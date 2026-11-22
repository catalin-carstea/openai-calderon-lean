module

public import Mathlib.MeasureTheory.Function.LpSpace.ContinuousFunctions
public import Mathlib.MeasureTheory.Integral.Bochner.Basic

import Mathlib.Tactic

public section

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace CalderonPaper.LowerGreen

theorem continuous_integral_of_joint_continuous
    {P S : Type} [TopologicalSpace P] [TopologicalSpace S] [CompactSpace S]
    [MeasurableSpace S] [BorelSpace S] (μ : Measure S) [IsFiniteMeasure μ]
    {f : P × S → ℝ} (hf : Continuous f) :
    Continuous (fun p : P => ∫ z, f (p,z) ∂μ) := by
  let A (p : P) : C(S,ℝ) :=
    ⟨fun z => f (p,z),hf.comp (continuous_const.prodMk continuous_id)⟩
  have hA : Continuous A := ContinuousMap.continuous_of_continuous_uncurry A hf
  let L := ContinuousMap.toLp (E := ℝ) 1 μ ℝ
  have h := (L1.integralCLM (α := S) (E := ℝ) (μ := μ)).continuous.comp
    (L.continuous.comp hA)
  refine h.congr (fun p => ?_)
  change L1.integralCLM (L (A p)) = _
  rw [← L1.integral_eq,L1.integral_eq_integral]
  exact integral_congr_ae (ContinuousMap.coeFn_toLp (p := 1) (𝕜 := ℝ) μ (A p))

end CalderonPaper.LowerGreen

end
