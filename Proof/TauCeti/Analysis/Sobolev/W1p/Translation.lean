/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Proof.TauCeti.Analysis.Sobolev.W1p.Basic
import Proof.TauCeti.Analysis.Sobolev.WeakDeriv.Translation
import Proof.TauCeti.MeasureTheory.Function.Lp.Translation

 













public section

noncomputable section

namespace TauCeti

open MeasureTheory Set TopologicalSpace
open scoped ENNReal Gradient InnerProductSpace

variable {E : Type*} [MeasurableSpace E] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [BorelSpace E] {mu : Measure E} [mu.IsAddHaarMeasure]
  {Omega : Opens E} {p : ENNReal} [Fact (1 ≤ p)]

 





def W1p.translate {Omega V : Opens E} {h : E} (hVO : MapsTo (· + h) V Omega)
    (u : W1p mu Omega p) : W1p mu V p := by
  let hv : MemLp (fun x => W1p.value u (x + h)) p (mu.restrict V) :=
    MeasureTheory.MemLp.comp_add_right_restrict_of_mapsTo (Lp.memLp (W1p.value u)) hVO
  let hg : MemLp (fun x => W1p.gradient u (x + h)) p (mu.restrict V) :=
    MeasureTheory.MemLp.comp_add_right_restrict_of_mapsTo (Lp.memLp (W1p.gradient u)) hVO
  let value := hv.toLp (fun x => W1p.value u (x + h))
  let gradient := hg.toLp (fun x => W1p.gradient u (x + h))
  refine W1p.mk value gradient ?_
  have hweak := (W1p.hasWeakFDerivOn u).comp_add_right hVO
  refine hweak.congr_ae hv.coeFn_toLp.symm |>.congr_ae_deriv ?_
  filter_upwards [hg.coeFn_toLp] with x hx
  rw [hx]

 
theorem W1p.value_translate_ae {Omega V : Opens E} {h : E}
    (hVO : MapsTo (· + h) V Omega) (u : W1p mu Omega p) :
    W1p.value (W1p.translate hVO u) =ᵐ[mu.restrict V] fun x => W1p.value u (x + h) := by
  simp only [W1p.translate, W1p.value_mk]
  exact MemLp.coeFn_toLp _

 

theorem W1p.gradient_translate_ae {Omega V : Opens E} {h : E}
    (hVO : MapsTo (· + h) V Omega) (u : W1p mu Omega p) :
    W1p.gradient (W1p.translate hVO u) =ᵐ[mu.restrict V]
      fun x => W1p.gradient u (x + h) := by
  simp only [W1p.translate, W1p.gradient_mk]
  exact MemLp.coeFn_toLp _

end TauCeti
