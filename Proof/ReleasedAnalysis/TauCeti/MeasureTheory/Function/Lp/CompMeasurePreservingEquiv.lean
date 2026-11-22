/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Function.LpSpace.ContinuousFunctions

/-! From Proof/TauCeti/MeasureTheory/Function/Lp/CompMeasurePreservingEquiv.lean in the Proposition 5.3 release
`f308cb9d8751b6590c8caa28736de77e063a41e1af8cad4e9dfa94819a8299b8`. Module layout adapted for Leanflow v2. -/

 




































public section

open scoped ENNReal

namespace MeasureTheory
namespace Lp

 




@[simp]
theorem compMeasurePreservingₗᵢ_apply {α β E : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ : Measure α} {μb : Measure β} {p : ℝ≥0∞} [NormedAddCommGroup E] {f : α → β}
    (𝕜 : Type*) [NormedRing 𝕜] [Module 𝕜 E] [IsBoundedSMul 𝕜 E] [Fact (1 ≤ p)]
    (hf : MeasurePreserving f μ μb) (x : Lp E p μb) :
    compMeasurePreservingₗᵢ 𝕜 f hf x = compMeasurePreserving f hf x :=
  rfl

 

theorem compMeasurePreserving_comp_apply_of_ae_id {α β E : Type*} [MeasurableSpace α]
    [MeasurableSpace β] {μ : Measure α} {μb : Measure β} {p : ℝ≥0∞} [NormedAddCommGroup E]
    {f : α → β} {g : β → α} (hf : MeasurePreserving f μ μb) (hg : MeasurePreserving g μb μ)
    (hfg : f ∘ g =ᵐ[μb] id) (x : Lp E p μb) :
    compMeasurePreserving g hg (compMeasurePreserving f hf x) = x := by
  rw [← compMeasurePreserving_comp_apply (E := E) (p := p) x hf hg]
  refine Subtype.ext ?_
  rw [compMeasurePreserving_val,
    AEEqFun.compMeasurePreserving_congr _ _ measurable_id hfg,
    AEEqFun.compMeasurePreserving_id]

 

@[simp]
theorem compMeasurePreserving_toLp {α β E : Type*} [TopologicalSpace α] [CompactSpace α]
    [MeasurableSpace α] [BorelSpace α] [TopologicalSpace β] [CompactSpace β] [MeasurableSpace β]
    [BorelSpace β] [NormedAddCommGroup E] [SecondCountableTopologyEither α E]
    [SecondCountableTopologyEither β E] {μ : Measure α} {μb : Measure β} [IsFiniteMeasure μ]
    [IsFiniteMeasure μb] {p : ℝ≥0∞} [Fact (1 ≤ p)] (𝕜 : Type*) [NormedRing 𝕜] [Module 𝕜 E]
    [IsBoundedSMul 𝕜 E] (F : C(β, E)) (φ : C(α, β)) (hφ : MeasurePreserving φ μ μb) :
    compMeasurePreserving φ hφ (ContinuousMap.toLp p μb 𝕜 F) =
      ContinuousMap.toLp p μ 𝕜 (F.comp φ) := by
  refine Lp.ext ((coeFn_compMeasurePreserving _ hφ).trans ?_)
  exact (hφ.quasiMeasurePreserving.ae_eq_comp
    (ContinuousMap.coeFn_toLp (𝕜 := 𝕜) (p := p) μb F)).trans
      (ContinuousMap.coeFn_toLp (𝕜 := 𝕜) (p := p) μ (F.comp φ)).symm

 













@[expose] noncomputable def compMeasurePreservingₗᵢEquiv {α β E : Type*} [MeasurableSpace α]
    [MeasurableSpace β] {μ : Measure α} {μb : Measure β} {p : ℝ≥0∞} [NormedAddCommGroup E]
    {f : α → β} {g : β → α}
    (𝕜 : Type*) [NormedRing 𝕜] [Module 𝕜 E] [IsBoundedSMul 𝕜 E] [Fact (1 ≤ p)]
    (hf : MeasurePreserving f μ μb) (hg : MeasurePreserving g μb μ) (hfg : f ∘ g =ᵐ[μb] id) :
    Lp E p μb ≃ₗᵢ[𝕜] Lp E p μ :=
  LinearIsometryEquiv.ofLinearIsometry (compMeasurePreservingₗᵢ 𝕜 f hf)
    (compMeasurePreservingₗ 𝕜 g hg)
    (LinearMap.ext fun x => (compMeasurePreservingₗᵢ 𝕜 g hg).injective
      (compMeasurePreserving_comp_apply_of_ae_id (E := E) (p := p) hf hg hfg
        (compMeasurePreserving g hg x)))
    (LinearMap.ext fun x => compMeasurePreserving_comp_apply_of_ae_id (E := E) (p := p) hf hg hfg x)

@[simp]
theorem compMeasurePreservingₗᵢEquiv_apply {α β E : Type*} [MeasurableSpace α]
    [MeasurableSpace β] {μ : Measure α} {μb : Measure β} {p : ℝ≥0∞} [NormedAddCommGroup E]
    {f : α → β} {g : β → α}
    (𝕜 : Type*) [NormedRing 𝕜] [Module 𝕜 E] [IsBoundedSMul 𝕜 E] [Fact (1 ≤ p)]
    (hf : MeasurePreserving f μ μb) (hg : MeasurePreserving g μb μ)
    (hfg : f ∘ g =ᵐ[μb] id) (x : Lp E p μb) :
    compMeasurePreservingₗᵢEquiv 𝕜 hf hg hfg x = compMeasurePreserving f hf x := by
  rw [compMeasurePreservingₗᵢEquiv, LinearIsometryEquiv.coe_ofLinearIsometry,
    compMeasurePreservingₗᵢ_apply]

@[simp]
theorem compMeasurePreservingₗᵢEquiv_symm_apply {α β E : Type*} [MeasurableSpace α]
    [MeasurableSpace β] {μ : Measure α} {μb : Measure β} {p : ℝ≥0∞} [NormedAddCommGroup E]
    {f : α → β} {g : β → α}
    (𝕜 : Type*) [NormedRing 𝕜] [Module 𝕜 E] [IsBoundedSMul 𝕜 E] [Fact (1 ≤ p)]
    (hf : MeasurePreserving f μ μb) (hg : MeasurePreserving g μb μ)
    (hfg : f ∘ g =ᵐ[μb] id) (x : Lp E p μ) :
    (compMeasurePreservingₗᵢEquiv 𝕜 hf hg hfg).symm x = compMeasurePreserving g hg x := by
  rw [compMeasurePreservingₗᵢEquiv, LinearIsometryEquiv.coe_ofLinearIsometry_symm]
  rfl

 
theorem coeFn_compMeasurePreservingₗᵢEquiv {α β E : Type*} [MeasurableSpace α]
    [MeasurableSpace β] {μ : Measure α} {μb : Measure β} {p : ℝ≥0∞} [NormedAddCommGroup E]
    {f : α → β} {g : β → α}
    (𝕜 : Type*) [NormedRing 𝕜] [Module 𝕜 E] [IsBoundedSMul 𝕜 E] [Fact (1 ≤ p)]
    (hf : MeasurePreserving f μ μb) (hg : MeasurePreserving g μb μ)
    (hfg : f ∘ g =ᵐ[μb] id) (x : Lp E p μb) :
    ⇑(compMeasurePreservingₗᵢEquiv 𝕜 hf hg hfg x) =ᵐ[μ] ⇑x ∘ f := by
  simpa using coeFn_compMeasurePreserving (E := E) (p := p) x hf

 
theorem coeFn_compMeasurePreservingₗᵢEquiv_symm {α β E : Type*} [MeasurableSpace α]
    [MeasurableSpace β] {μ : Measure α} {μb : Measure β} {p : ℝ≥0∞} [NormedAddCommGroup E]
    {f : α → β} {g : β → α}
    (𝕜 : Type*) [NormedRing 𝕜] [Module 𝕜 E] [IsBoundedSMul 𝕜 E] [Fact (1 ≤ p)]
    (hf : MeasurePreserving f μ μb) (hg : MeasurePreserving g μb μ)
    (hfg : f ∘ g =ᵐ[μb] id) (x : Lp E p μ) :
    ⇑((compMeasurePreservingₗᵢEquiv 𝕜 hf hg hfg).symm x) =ᵐ[μb] ⇑x ∘ g := by
  simpa using coeFn_compMeasurePreserving (E := E) (p := p) x hg

end Lp
end MeasureTheory
