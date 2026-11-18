/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Proof.TauCeti.Analysis.Sobolev.Wkp.Restriction
public import Proof.TauCeti.MeasureTheory.Function.Lp.LocalApproximateIdentity

 













public section

noncomputable section

namespace TauCeti

open Filter MeasureTheory Set TopologicalSpace
open scoped ENNReal

variable {E : Type*} [MeasurableSpace E] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [BorelSpace E] {mu : Measure E} [mu.IsAddHaarMeasure]
  {Omega U : Opens E} {p : ENNReal} [Fact (1 ≤ p)]

local instance : (mu.restrict (univ : Set E)).IsAddHaarMeasure := by
  rw [Measure.restrict_univ]
  infer_instance

 

theorem Wkp.tendsto_mollified_value (hp : p ≠ ∞) (hU : U ≤ Omega)
    {I : Type*} {l : Filter I} {phi : I → ContDiffBump (0 : E)}
    (hphi : Tendsto (fun i => (phi i).rOut) l (nhds 0))
    (k : ℕ) (u : Wkp mu Omega p k) :
    Tendsto (fun i =>
      Lp.LpToLpOfMeasureLeSMul (c := 1) (by simp) (by
        simpa only [one_smul] using Measure.restrict_mono_set mu
          (subset_univ (U : Set E))) <|
        normedBumpLp hp (phi i) (mu.restrict (univ : Set E))
          (extendByZeroLpₗᵢ ℝ mu Omega.isOpen.measurableSet (subset_univ _)
            (Wkp.value k u))) l (nhds (Wkp.value k (Wkp.restrictL hU k u))) := by
  rw [Wkp.value_restrictL]
  exact tendsto_normedBumpLp_extendByZero_restrict hp Omega.isOpen.measurableSet
    (SetLike.coe_subset_coe.mpr hU) hphi (Wkp.value k u)

 


theorem Wkp.tendsto_mollified_iteratedGradient (hp : p ≠ ∞) (hU : U ≤ Omega)
    {I : Type*} {l : Filter I} {phi : I → ContDiffBump (0 : E)}
    (hphi : Tendsto (fun i => (phi i).rOut) l (nhds 0))
    (k : ℕ) (u : Wkp mu Omega p (k + 1)) :
    Tendsto (fun i =>
      Lp.LpToLpOfMeasureLeSMul (c := 1) (by simp) (by
        simpa only [one_smul] using Measure.restrict_mono_set mu
          (subset_univ (U : Set E))) <|
        normedBumpLp hp (phi i) (mu.restrict (univ : Set E))
          (extendByZeroLpₗᵢ ℝ mu Omega.isOpen.measurableSet (subset_univ _)
            (Wkp.iteratedGradient k u))) l
      (nhds (Wkp.iteratedGradient k (Wkp.restrictL hU (k + 1) u))) := by
  rw [Wkp.iteratedGradient_restrictL]
  exact tendsto_normedBumpLp_extendByZero_restrict hp Omega.isOpen.measurableSet
    (SetLike.coe_subset_coe.mpr hU) hphi
    (Wkp.iteratedGradient k u)

end TauCeti
