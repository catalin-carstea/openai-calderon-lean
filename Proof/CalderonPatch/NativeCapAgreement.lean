module

public import Proof.CalderonPatch.CapSolutionAgreement
public import Proof.CalderonPatch.GlobalFromNativeCapSources

import Mathlib.Tactic

public section
noncomputable section
open MeasureTheory Set
open scoped ContDiff Manifold

namespace CalderonPatch

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [T2Space M] [CompactSpace M]
  [ChartedSpace (EuclideanHalfSpace (n+1)) M] [IsManifold (𝓡∂ (n+1)) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [ConnectedSpace M]

local notation "N" => (n+1)
local notation "J" => 𝓡∂ N

variable {d₁ d₂ : DirichletData n M} {Γ : Set ((𝓡∂ (n+1)).boundary M)}

namespace MeasuredCommonCap

variable (C : MeasuredCommonCap d₁ d₂ Γ)

@[expose] def firstData (μ : Measure M) (hμ : IsMetricVolume C.firstMetric μ) : DirichletData n M :=
  ⟨C.firstMetric,μ,hμ,d₁.boundary_nonempty⟩

@[expose] def secondData (μ : Measure M) (hμ : IsMetricVolume C.secondMetric μ) : DirichletData n M :=
  ⟨C.secondMetric,μ,hμ,d₂.boundary_nonempty⟩

variable {C}

/-- The common cap comparison applies to each label of the native
source family used by the global continuation. -/
theorem nativeCap_inverse_agreement
    (hEnergy : PatchEnergyEqual d₁.metric d₂.metric d₁.volume d₂.volume Γ)
    (S : C.SignedInteriorCharts) {μ₁ μ₂ : Measure M}
    (hμ₁ : IsMetricVolume C.firstMetric μ₁) (hμ₂ : IsMetricVolume C.secondMetric μ₂)
    (Q : NativeCapSourceCharts (C.firstData μ₁ hμ₁) (C.secondData μ₂ hμ₂) C.capMap) :
    NativeCapSourceAgreement Q (nativeInverseRegularity (C.firstData μ₁ hμ₁))
      (nativeInverseRegularity (C.secondData μ₂ hμ₂)) := by
  intro p hp f
  let D₁ := C.firstData μ₁ hμ₁
  let D₂ := C.secondData μ₂ hμ₂
  let r₁ := nativeInverseRegularity D₁
  let r₂ := nativeInverseRegularity D₂
  let q₁ := smoothChartSource Q.first Q.closure_first f
  let q₂ := smoothChartSource Q.second Q.closure_second f
  let u₁ := D₁.smoothInverse r₁ q₁
  let u₂ := D₂.smoothInverse r₂ q₂
  obtain ⟨hu₁,hz₁,hEq₁,_⟩ := D₁.smoothInverse_spec r₁ q₁
  obtain ⟨hu₂,hz₂,hEq₂,_⟩ := D₂.smoothInverse_spec r₂ q₂
  have hH₁ : EqOn (nativeLaplace C.firstMetric u₁) 0 ((J).interior M \ closure C.capMap.target) := by
    intro x hx
    have hf := Q.source_first_eq_zero_off_cap f (fun h => hx.2 (subset_closure h))
    exact neg_eq_zero.mp ((hEq₁ hx.1).trans hf)
  have hH₂ : EqOn (nativeLaplace C.secondMetric u₂) 0 ((J).interior M \ closure C.capMap.source) := by
    intro x hx
    have hf := Q.source_second_eq_zero_off_cap f (fun h => hx.2 (subset_closure h))
    exact neg_eq_zero.mp ((hEq₂ hx.1).trans hf)
  have hCap : EqOn (nativeLaplace C.firstMetric u₁ ∘ C.capMap) (nativeLaplace C.secondMetric u₂) C.capMap.source := by
    intro x hx
    have hEq := (hEq₁ (C.target_interior (C.capMap.map_source hx))).trans <|
      (Q.source_eqOn f hx).symm.trans (hEq₂ (C.source_interior hx)).symm
    exact neg_injective hEq
  exact (MeasuredCommonCap.cap_solution_agreement S hEnergy hu₁ hu₂ hz₁ hz₂ hH₁ hH₂ hCap hp).symm

end MeasuredCommonCap

end CalderonPatch
