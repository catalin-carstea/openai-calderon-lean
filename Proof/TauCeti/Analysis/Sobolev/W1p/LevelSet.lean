/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Proof.TauCeti.Analysis.Sobolev.W1p.ChainRule

import Mathlib.Algebra.Order.Group.PosPart

 












public section

namespace TauCeti

open Filter MeasureTheory Set TopologicalSpace
open scoped ENNReal InnerProductSpace

variable {E : Type*} [MeasurableSpace E] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [BorelSpace E] {mu : Measure E} [mu.IsAddHaarMeasure]
  {Omega : Opens E} {p : ENNReal} [Fact (1 ≤ p)]

 

theorem W1p.gradient_ae_eq_zero_on_level_set (hp : p ≠ ∞) (u : W1p mu Omega p) (k : ℝ) :
    ∀ᵐ x ∂mu.restrict Omega, W1p.value u x = k → W1p.gradient u x = 0 := by
  classical
  have hneg : ⇑(W1p.value (-u)) =ᵐ[mu.restrict Omega] -W1p.value u := by
    simpa only [← W1p.valueL_apply, map_neg] using Lp.coeFn_neg (W1p.value u)
  have hconst : HasWeakFDerivOn mu Omega (fun _ : E => k) 0 :=
    hasWeakFDerivOn_iff.2 fun _ => hasWeakLineDerivOn_const k
  have hsplit := (W1p.hasWeakFDerivOn_posPartAbove hp k u).sub
    (W1p.hasWeakFDerivOn_posPartAbove hp (-k) (-u))
  have hvalue :
      (fun x => max (W1p.value u x - k) 0) -
          (fun x => max (W1p.value (-u) x - -k) 0) =ᵐ[mu.restrict Omega]
        (fun x => W1p.value u x - k) := by
    filter_upwards [hneg] with x hx
    simpa only [Pi.sub_apply, hx, Pi.neg_apply, neg_sub_neg, posPart_def, negPart_def,
      neg_sub] using posPart_sub_negPart (W1p.value u x - k)
  have hderiv := ((W1p.hasWeakFDerivOn u).sub hconst).ae_eq (hsplit.congr_ae hvalue)
  filter_upwards [hneg, hderiv] with x hnegx hx
  intro hlevel
  have hpos : {y | k < W1p.value u y}.indicator (⇑(W1p.gradient u)) x = 0 :=
    indicator_of_notMem (by simpa only [mem_ofPred_eq, hlevel] using lt_irrefl k) _
  have hneg : {y | -k < W1p.value (-u) y}.indicator (⇑(W1p.gradient (-u))) x = 0 :=
    indicator_of_notMem
      (by simpa only [mem_ofPred_eq, hnegx, Pi.neg_apply, hlevel] using lt_irrefl (-k)) _
  have hz : innerSL ℝ (W1p.gradient u x) = 0 := by
    simpa only [Pi.sub_apply, Pi.zero_apply, sub_zero, hpos, hneg, map_zero] using hx
  exact innerSL_inj.mp (hz.trans (map_zero _).symm)

 

theorem W1p.gradient_ae_eq_on_eq (hp : p ≠ ∞) (u v : W1p mu Omega p) :
    ∀ᵐ x ∂mu.restrict Omega,
      W1p.value u x = W1p.value v x → W1p.gradient u x = W1p.gradient v x := by
  have hvalue : ⇑(W1p.value (u - v)) =ᵐ[mu.restrict Omega]
      W1p.value u - W1p.value v := by
    simpa only [← W1p.valueL_apply, map_sub] using Lp.coeFn_sub (W1p.value u) (W1p.value v)
  have hgradient : ⇑(W1p.gradient (u - v)) =ᵐ[mu.restrict Omega]
      W1p.gradient u - W1p.gradient v := by
    simpa only [← W1p.gradientL_apply, map_sub] using Lp.coeFn_sub (W1p.gradient u) (W1p.gradient v)
  filter_upwards [W1p.gradient_ae_eq_zero_on_level_set hp (u - v) 0, hvalue, hgradient]
    with x hx hux hgx
  intro h
  apply sub_eq_zero.mp
  simpa only [hgx, Pi.sub_apply] using hx (by simp [hux, h])

end TauCeti
