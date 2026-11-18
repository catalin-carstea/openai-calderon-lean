/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Proof.TauCeti.Analysis.Sobolev.WeakDeriv.Basic
public import Proof.TauCeti.MeasureTheory.Function.LocallyIntegrable
import Mathlib.Topology.Separation.Regular

 



















public section

open MeasureTheory Set TopologicalSpace
open scoped Distributions

namespace TauCeti

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [LocallyCompactSpace E]
  [MeasurableSpace E] {μ : Measure E} {Ω : Opens E} {u u' : E → F} {v : E}

 



theorem hasWeakLineDerivOn_iff_forall_isCompact_closure :
    HasWeakLineDerivOn μ Ω u u' v ↔
      ∀ V : Opens E, IsCompact (closure (V : Set E)) → closure (V : Set E) ⊆ Ω →
        HasWeakLineDerivOn μ V u u' v := by
  constructor
  · intro h V _ hV
    exact h.mono (subset_closure.trans hV)
  · intro h
    have hc : CompleteSpace F :=
      (h ⊥ (by simp) (by simp)).completeSpace
    refine hasWeakLineDerivOn_iff_testFunction.2 ⟨hc,
      locallyIntegrableOn_iff_forall_isCompact_closure.2
        (fun V hVc hVΩ => (h V hVc hVΩ).locallyIntegrableOn),
      locallyIntegrableOn_iff_forall_isCompact_closure.2
        (fun V hVc hVΩ => (h V hVc hVΩ).locallyIntegrableOn_deriv), ?_⟩
    intro φ
    obtain ⟨V, hVo, hφV, hVΩ, hVc⟩ :=
      exists_open_between_and_isCompact_closure φ.hasCompactSupport Ω.isOpen φ.tsupport_subset
    exact (h ⟨V, hVo⟩ hVc hVΩ).integral_lineDeriv_smul_eq_neg_integral_smul
      ⟨φ, φ.contDiff, φ.hasCompactSupport, hφV⟩

 


theorem hasWeakFDerivOn_iff_forall_isCompact_closure {U : E → E →L[ℝ] F} :
    HasWeakFDerivOn μ Ω u U ↔
      ∀ V : Opens E, IsCompact (closure (V : Set E)) → closure (V : Set E) ⊆ Ω →
        HasWeakFDerivOn μ V u U := by
  constructor
  · intro h V _ hV
    exact h.mono (subset_closure.trans hV)
  · intro h
    refine hasWeakFDerivOn_iff.2 fun v =>
      hasWeakLineDerivOn_iff_forall_isCompact_closure.2 ?_
    intro V hVc hVΩ
    exact (h V hVc hVΩ).hasWeakLineDerivOn v

end TauCeti
