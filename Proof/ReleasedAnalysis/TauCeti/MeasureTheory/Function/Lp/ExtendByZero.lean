/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Function.LpSpace.Basic
public import Mathlib.MeasureTheory.Function.LpSeminorm.Indicator

/-! From Proof/TauCeti/MeasureTheory/Function/Lp/ExtendByZero.lean in the Proposition 5.3 release
`f308cb9d8751b6590c8caa28736de77e063a41e1af8cad4e9dfa94819a8299b8`. Module layout adapted for Leanflow v2. -/

 





























public section

noncomputable section

namespace TauCeti

open MeasureTheory Set

open scoped ENNReal

variable {α : Type*} [MeasurableSpace α] {F : Type*} [NormedAddCommGroup F] (𝕜 : Type*)
  [NormedRing 𝕜] [Module 𝕜 F] [IsBoundedSMul 𝕜 F] {p : ℝ≥0∞} {μ : Measure α} {s t : Set α}

variable (μ) in
 
@[expose] def extendByZeroLpₗ (hs : MeasurableSet s) :
    Lp F p (μ.restrict s) →ₗ[𝕜] Lp F p (μ.restrict t) where
  toFun f := (((memLp_indicator_iff_restrict hs.nullMeasurableSet).2 (Lp.memLp f)).mono_measure
    Measure.restrict_le_self).toLp _
  map_add' f g := by
    rw [← MemLp.toLp_add]
    exact MemLp.toLp_congr _ _
      (ae_restrict_of_ae (((ae_eq_restrict_iff_indicator_ae_eq hs).mp
        (Lp.coeFn_add f g)).trans (.of_eq (indicator_add' s _ _))))
  map_smul' c f := by
    rw [RingHom.id_apply, ← MemLp.toLp_const_smul]
    exact MemLp.toLp_congr _ _
      (ae_restrict_of_ae (((ae_eq_restrict_iff_indicator_ae_eq hs).mp
        (Lp.coeFn_smul c f)).trans (.of_eq (indicator_const_smul s c _))))

variable (μ) in
 





@[expose] def extendByZeroLpₗᵢ [Fact (1 ≤ p)] (hs : MeasurableSet s) (hst : s ⊆ t) :
    Lp F p (μ.restrict s) →ₗᵢ[𝕜] Lp F p (μ.restrict t) where
  toLinearMap := extendByZeroLpₗ 𝕜 μ hs
  norm_map' f := by
     
     
    change ‖(extendByZeroLpₗ 𝕜 μ hs f)‖ = ‖f‖
    dsimp [extendByZeroLpₗ]
    rw [Lp.norm_toLp, eLpNorm_indicator_eq_eLpNorm_restrict hs.nullMeasurableSet,
      Measure.restrict_restrict_of_subset hst, ← Lp.norm_def]

 
theorem coeFn_extendByZeroLpₗᵢ [Fact (1 ≤ p)] (hs : MeasurableSet s) (hst : s ⊆ t)
    (f : Lp F p (μ.restrict s)) :
    (extendByZeroLpₗᵢ 𝕜 μ hs hst f : α → F) =ᵐ[μ.restrict t] s.indicator (f : α → F) :=
  MemLp.coeFn_toLp
    (((memLp_indicator_iff_restrict hs.nullMeasurableSet).2 (Lp.memLp f)).mono_measure
      Measure.restrict_le_self)

 
theorem coeFn_extendByZeroLpₗᵢ_restrict [Fact (1 ≤ p)] (hs : MeasurableSet s) (hst : s ⊆ t)
    (f : Lp F p (μ.restrict s)) :
    (extendByZeroLpₗᵢ 𝕜 μ hs hst f : α → F) =ᵐ[μ.restrict s] (f : α → F) :=
  ((coeFn_extendByZeroLpₗᵢ 𝕜 hs hst f).filter_mono
    (ae_mono (Measure.restrict_mono hst le_rfl))).trans
    (indicator_ae_eq_restrict hs.nullMeasurableSet)

 
@[simp]
theorem extendByZeroLpₗᵢ_self [Fact (1 ≤ p)] (hs : MeasurableSet s)
    (f : Lp F p (μ.restrict s)) : extendByZeroLpₗᵢ 𝕜 μ hs Subset.rfl f = f :=
  Lp.ext (coeFn_extendByZeroLpₗᵢ_restrict 𝕜 hs Subset.rfl f)

 

@[simp]
theorem extendByZeroLpₗᵢ_extendByZeroLpₗᵢ [Fact (1 ≤ p)] {u : Set α} (hs : MeasurableSet s)
    (ht : MeasurableSet t) (hst : s ⊆ t) (htu : t ⊆ u) (f : Lp F p (μ.restrict s)) :
    extendByZeroLpₗᵢ 𝕜 μ ht htu (extendByZeroLpₗᵢ 𝕜 μ hs hst f) =
      extendByZeroLpₗᵢ 𝕜 μ hs (hst.trans htu) f := by
  refine Lp.ext ?_
  filter_upwards [coeFn_extendByZeroLpₗᵢ 𝕜 ht htu (extendByZeroLpₗᵢ 𝕜 μ hs hst f),
    ae_restrict_of_ae ((ae_eq_restrict_iff_indicator_ae_eq ht).mp
      (coeFn_extendByZeroLpₗᵢ 𝕜 hs hst f)),
    coeFn_extendByZeroLpₗᵢ 𝕜 hs (hst.trans htu) f] with x h1 h2 h3
  rw [h1, h2, h3, indicator_indicator, inter_eq_self_of_subset_right hst]

 


theorem extendByZeroLpₗᵢ_eq_of_ae_eq [Fact (1 ≤ p)] (hs : MeasurableSet s) (hst : s ⊆ t)
    {h : α → F} (hsupp : Function.support h ⊆ s) {f : Lp F p (μ.restrict s)}
    {g : Lp F p (μ.restrict t)} (hf : ∀ᵐ x ∂μ.restrict s, f x = h x)
    (hg : ∀ᵐ x ∂μ.restrict t, g x = h x) : extendByZeroLpₗᵢ 𝕜 μ hs hst f = g :=
  Lp.ext <| ((coeFn_extendByZeroLpₗᵢ 𝕜 hs hst f).trans
    (ae_restrict_of_ae (((ae_eq_restrict_iff_indicator_ae_eq hs).mp hf).trans
      (.of_eq (indicator_eq_self.2 hsupp))))).trans
    (Filter.EventuallyEq.symm hg)

 



theorem coeFn_extendByZeroLpₗᵢ_comp {G : Type*} [NormedAddCommGroup G] [Module 𝕜 G]
    [IsBoundedSMul 𝕜 G] {q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)]
    (hs : MeasurableSet s) (hst : s ⊆ t) (L : F → G)
    (hL : L 0 = 0) {f : Lp F p (μ.restrict s)} {g' : Lp G q (μ.restrict s)}
    (hg' : ∀ᵐ x ∂μ.restrict s, g' x = L (f x)) :
    (extendByZeroLpₗᵢ 𝕜 μ hs hst g' : α → G) =ᵐ[μ.restrict t]
      fun x => L (extendByZeroLpₗᵢ 𝕜 μ hs hst f x) := by
  filter_upwards [coeFn_extendByZeroLpₗᵢ 𝕜 hs hst g', coeFn_extendByZeroLpₗᵢ 𝕜 hs hst f,
    ae_restrict_of_ae ((ae_eq_restrict_iff_indicator_ae_eq hs).mp hg')] with x h1 h2 h3
  rw [h1, h3, h2]
  exact congrFun (Set.indicator_comp_of_zero hL) x

end TauCeti
