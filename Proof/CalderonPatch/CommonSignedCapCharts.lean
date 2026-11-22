module

public import Proof.CalderonPatch.MeasuredCapReadings
public import Proof.CalderonPatch.ChartDensity

import Mathlib.Tactic

public section
noncomputable section
open Filter MeasureTheory Set
open scoped ContDiff Manifold

namespace CalderonPatch

open CalderonN (I X chartVolume InteriorMetricChart)

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace (n+1)) M] [IsManifold (𝓡∂ (n+1)) ∞ M]
  [MeasurableSpace M] [BorelSpace M]

local notation "N" => (n+1)
local notation "E" => X N
local notation "J" => 𝓡∂ N
local notation "K" => 𝓘(ℝ, X N)
local notation "H" => inwardHalfSpace N
local notation "L" => (inwardChartSplit (n := N))

variable {d₁ d₂ : DirichletData n M} {Γ : Set ((𝓡∂ (n+1)).boundary M)}

namespace MeasuredCommonCap

variable (C : MeasuredCommonCap d₁ d₂ Γ)

/-- Both actual open cap charts use the same unpushed domain. -/
structure SignedInteriorCharts where
  first : OpenPartialHomeomorph M E
  second : OpenPartialHomeomorph M E
  first_source : first.source = C.capMap.target
  second_source : second.source = C.capMap.source
  first_target : first.target = signedCap C.signedHeight
  second_target : second.target = signedCap C.signedHeight
  first_inverse : (first.symm : E → M) = C.productFirst.coord.symm ∘ C.coordinates.push ∘ L
  second_inverse : (second.symm : E → M) = C.productSecond.coord.symm ∘ C.coordinates.push ∘ L
  first_smooth : ContMDiffOn J K ∞ first first.source
  second_smooth : ContMDiffOn J K ∞ second second.source
  first_inverse_smooth : ContMDiffOn K J ∞ first.symm first.target
  second_inverse_smooth : ContMDiffOn K J ∞ second.symm second.target
  first_field : EqOn (coordinateMetric C.firstMetric first) C.coordinates.first.field (signedCap C.signedHeight)
  second_field : EqOn (coordinateMetric C.secondMetric second) C.coordinates.second.field (signedCap C.signedHeight)

theorem exists_signedInteriorCharts : Nonempty C.SignedInteriorCharts := by
  have hS := C.signedCap_subset_box.trans C.signedBox_subset
  obtain ⟨e₁,h₁s,h₁t,_,h₁i,h₁,h₁si,h₁g⟩ := C.coordinates.first.exists_signedInteriorChart
    C.isOpen_signedCap hS C.signedCap_push_iff C.coordinates.smooth_push C.coordinates.smooth_push_inverse
  obtain ⟨e₂,h₂s,h₂t,_,h₂i,h₂,h₂si,h₂g⟩ := C.coordinates.second.exists_signedInteriorChart
    C.isOpen_signedCap hS C.signedCap_push_iff C.coordinates.smooth_push C.coordinates.smooth_push_inverse
  exact ⟨⟨e₁,e₂,h₁s,h₂s,h₁t,h₂t,h₁i,h₂i,h₁,h₂,h₁si,h₂si,h₁g,h₂g⟩⟩

variable {C} (S : C.SignedInteriorCharts)

omit [BorelSpace M] in
theorem SignedInteriorCharts.first_interior : S.first.source ⊆ (J).interior M := by
  rw [S.first_source]
  exact C.target_interior

omit [BorelSpace M] in
theorem SignedInteriorCharts.second_interior : S.second.source ⊆ (J).interior M := by
  rw [S.second_source]
  exact C.source_interior

omit [BorelSpace M] in
theorem SignedInteriorCharts.same_inverse :
    EqOn S.first.symm (C.capMap ∘ S.second.symm) (signedCap C.signedHeight) := by
  intro x hx
  have hx' : C.coordinates.push (L x) ∈ pushedCap C.coordinates.height := (C.signedCap_push_iff x).mpr hx
  have hp := C.coordinates.second.push_mem_target (C.signedBox_subset (C.signedCap_subset_box hx)) hx'.1.le
  rw [S.first_inverse,S.second_inverse,C.coordinates.charts_map]
  change C.productFirst.coord.symm (C.coordinates.push (L x)) =
    C.productFirst.coord.symm (C.productSecond.coord (C.productSecond.coord.symm (C.coordinates.push (L x))))
  rw [C.productSecond.coord.right_inv hp]

omit [BorelSpace M] in
theorem SignedInteriorCharts.same_field :
    EqOn (coordinateMetric C.firstMetric S.first) (coordinateMetric C.secondMetric S.second)
      (signedCap C.signedHeight) := by
  intro x hx
  have hxH : x ∈ Hᶜ := fun h => (not_le_of_gt hx.2) h
  exact (S.first_field hx).trans <|
    (C.coordinates.fields_eq hxH).trans (S.second_field hx).symm

/-- The volume and the coordinate operator of the first cap agree
with its native metric data. -/
@[expose] def SignedInteriorCharts.firstMetricChart (μ : Measure M) (hμ : IsMetricVolume C.firstMetric μ) :
    InteriorMetricChart J μ (nativeLaplace C.firstMetric) :=
  nativeInteriorMetricChart C.firstMetric μ hμ S.first S.first_interior S.first_smooth S.first_inverse_smooth

/-- The volume and the coordinate operator of the second cap agree
with its native metric data. -/
@[expose] def SignedInteriorCharts.secondMetricChart (μ : Measure M) (hμ : IsMetricVolume C.secondMetric μ) :
    InteriorMetricChart J μ (nativeLaplace C.secondMetric) :=
  nativeInteriorMetricChart C.secondMetric μ hμ S.second S.second_interior S.second_smooth S.second_inverse_smooth

end MeasuredCommonCap

end CalderonPatch
