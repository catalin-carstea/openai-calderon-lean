/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Proof.ReleasedAnalysis.TauCeti.Analysis.Calculus.BumpFunction.Average
public import Proof.ReleasedAnalysis.TauCeti.MeasureTheory.Function.Lp.Translation

/-! From Proof/TauCeti/MeasureTheory/Function/Lp/ApproximateIdentity.lean in the Proposition 5.3 release
`f308cb9d8751b6590c8caa28736de77e063a41e1af8cad4e9dfa94819a8299b8`. Module layout adapted for Leanflow v2. -/

 









































public section

noncomputable section

namespace TauCeti

open ContinuousLinearMap Filter MeasureTheory Metric Set
open scoped Convolution ENNReal

variable {E F : Type*} [MeasurableSpace E] [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [BorelSpace E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  {mu : Measure E} [mu.IsAddHaarMeasure] {p : ENNReal} [Fact (1 ≤ p)]

 












@[expose] def normedBumpLp (hp : p ≠ ∞) (phi : ContDiffBump (0 : E))
    (mu : Measure E) [mu.IsAddHaarMeasure] : Lp F p mu →L[ℝ] Lp F p mu :=
  normedBumpAverageL phi mu (mu.translateLp p) (Measure.continuous_translateLp hp)

 
theorem normedBumpLp_apply (hp : p ≠ ∞) (phi : ContDiffBump (0 : E)) (f : Lp F p mu) :
    normedBumpLp hp phi mu f =
      ∫ t, phi.normed mu t • mu.translateLp p (-t) f ∂mu := by
  exact normedBumpAverageL_apply (F := Lp F p mu) phi mu (mu.translateLp p)
    (Measure.continuous_translateLp hp) f

 
theorem normedBumpLp_eq_normedBumpAverageL (hp : p ≠ ∞) (phi : ContDiffBump (0 : E)) :
    normedBumpLp (F := F) hp phi mu =
      normedBumpAverageL phi mu (mu.translateLp p) (Measure.continuous_translateLp hp) :=
  (rfl)

 

theorem compLpL_normedBumpLp {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    [CompleteSpace F] [CompleteSpace G] (hp : p ≠ ∞) (phi : ContDiffBump (0 : E))
    (L : F →L[ℝ] G) (f : Lp F p mu) :
    L.compLpL p mu (normedBumpLp hp phi mu f) = normedBumpLp hp phi mu (L.compLpL p mu f) :=
  normedBumpAverageL_comm _ _ _ _ _ _ _ (Measure.compLpL_translateLp L) f

 

theorem norm_normedBumpLp_le_one (hp : p ≠ ∞) (phi : ContDiffBump (0 : E)) :
    ‖normedBumpLp (F := F) hp phi mu‖ ≤ 1 := by
  exact norm_normedBumpAverageL_le_one (F := Lp F p mu) phi mu (mu.translateLp p)
    (Measure.continuous_translateLp hp)

 







theorem tendsto_normedBumpLp [CompleteSpace F] {I : Type*} {l : Filter I}
    (hp : p ≠ ∞) {phi : I → ContDiffBump (0 : E)}
    (hphi : Tendsto (fun i ↦ (phi i).rOut) l (nhds 0)) (f : Lp F p mu) :
    Tendsto (fun i ↦ normedBumpLp hp (phi i) mu f) l (nhds f) := by
  simpa only [normedBumpLp, Measure.translateLp_zero] using
    tendsto_normedBumpAverageL (F := Lp F p mu) hphi mu (mu.translateLp p)
      (Measure.continuous_translateLp hp) f

end TauCeti
