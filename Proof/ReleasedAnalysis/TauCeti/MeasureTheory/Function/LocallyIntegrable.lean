/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Group.Measure
import Mathlib.Topology.Separation.Regular

/-! From Proof/TauCeti/MeasureTheory/Function/LocallyIntegrable.lean in the Proposition 5.3 release
`f308cb9d8751b6590c8caa28736de77e063a41e1af8cad4e9dfa94819a8299b8`. Module layout adapted for Leanflow v2. -/

 



































public section

open MeasureTheory Set TopologicalSpace

namespace MeasureTheory

variable {E F : Type*} [MeasurableSpace E] [AddGroup E] [TopologicalSpace E]
  [ContinuousAdd E] [BorelSpace E]
  [TopologicalSpace F] [ContinuousENorm F] {mu : Measure E} [mu.IsAddRightInvariant]
  {Omega V : Set E} {u : E → F} {h : E}

 

theorem LocallyIntegrableOn.comp_add_right_of_mapsTo
    (hu : LocallyIntegrableOn u Omega mu) (hVO : MapsTo (· + h) V Omega) :
    LocallyIntegrableOn (fun x => u (x + h)) V mu := by
  intro x hx
  obtain ⟨s, hs, hus⟩ := hu (x + h) (hVO hx)
  refine ⟨(· + h) ⁻¹' s, ?_, ?_⟩
  · exact ((continuous_id.add continuous_const).continuousWithinAt.tendsto_nhdsWithin hVO) hs
  · simpa only [Function.comp_def] using
      ((measurePreserving_add_right mu h).integrableOn_comp_preimage
        (Homeomorph.addRight h).measurableEmbedding).2 hus

end MeasureTheory

namespace TauCeti

variable {X : Type*} [MeasurableSpace X] [TopologicalSpace X] {μ : Measure X}

section RelativelyCompactSubdomains

variable {ε : Type*} [TopologicalSpace ε] [ContinuousENorm ε]
  [LocallyCompactSpace X] [RegularSpace X] {f : X → ε} {Ω : Opens X}

 

theorem locallyIntegrableOn_iff_forall_isCompact_closure :
    LocallyIntegrableOn f Ω μ ↔
      ∀ V : Opens X, IsCompact (closure (V : Set X)) → closure (V : Set X) ⊆ Ω →
        LocallyIntegrableOn f V μ := by
  constructor
  · intro hf V _ hV
    exact hf.mono_set (subset_closure.trans hV)
  · intro h x hx
    obtain ⟨V, hVo, hxV, hVΩ, hVc⟩ :=
      exists_open_between_and_isCompact_closure isCompact_singleton Ω.isOpen
        (singleton_subset_iff.mpr hx)
    have hf := h ⟨V, hVo⟩ hVc hVΩ x (hxV (mem_singleton x))
    simp only [Opens.coe_mk, hVo.nhdsWithin_eq (hxV (mem_singleton x))] at hf
    exact hf.filter_mono nhdsWithin_le_nhds

end RelativelyCompactSubdomains

end TauCeti

namespace MeasureTheory.LocallyIntegrableOn

variable {X : Type*} [MeasurableSpace X] [TopologicalSpace X] {μ : Measure X}

section ExtendByZero

variable {ε : Type*} [TopologicalSpace ε] [ESeminormedAddMonoid ε] [PseudoMetrizableSpace ε]
  {f : X → ε} {s K : Set X}

 






theorem integrable_indicator_of_isCompact (hloc : LocallyIntegrableOn f s μ)
    (hs : NullMeasurableSet s μ) (hK : IsCompact K)
    (hKmeas : NullMeasurableSet K μ) (hKs : K ⊆ s)
    (hf : ∀ᵐ x ∂μ.restrict s, x ∉ K → f x = 0) :
    Integrable (s.indicator f) μ := by
  have hae : s.indicator f =ᵐ[μ] K.indicator f := by
    filter_upwards [(ae_restrict_iff'₀ hs).1 hf] with x hx
    by_cases hxs : x ∈ s
    · by_cases hxK : x ∈ K
      · rw [Set.indicator_of_mem hxs, Set.indicator_of_mem hxK]
      · rw [Set.indicator_of_mem hxs, Set.indicator_of_notMem hxK, hx hxs hxK]
    · rw [Set.indicator_of_notMem hxs, Set.indicator_of_notMem fun hxK => hxs (hKs hxK)]
  exact ((hloc.integrableOn_compact_subset hKs hK).integrable_indicator₀ hKmeas).congr hae.symm

end ExtendByZero

end MeasureTheory.LocallyIntegrableOn
