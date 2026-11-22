module

public import Proof.CalderonPatch.Energy

import Proof.CalderonPatch.NativeCapAgreement
import Proof.CalderonPatch.MetricVolumeChange
import Proof.CalderonPatch.OriginalFromInterior
import Proof.CalderonPatch.MeasuredAccessibleGauge
import Mathlib.Tactic

public section

open Filter Metric Set MeasureTheory
open scoped ContDiff Manifold

namespace CalderonPatch

/-- Theorem 1.1, in the equivalent smooth quadratic Dirichlet energy formulation. -/
theorem smoothAnisotropicUniqueness {n : ℕ} [NeZero n] (hn : 3 ≤ n)
    {M : Type*} [TopologicalSpace M] [T2Space M] [CompactSpace M] [ConnectedSpace M]
    [ChartedSpace (EuclideanHalfSpace n) M] [IsManifold (𝓡∂ n) ∞ M]
    [MeasurableSpace M] [BorelSpace M]
    {Γ : Set ((𝓡∂ n).boundary M)} (hΓ : IsOpen Γ) (hΓne : Γ.Nonempty) (hΓproper : Γ ≠ univ)
    {g₁ g₂ : SmoothMetric n M} {μ₁ μ₂ : Measure M}
    (hμ₁ : IsMetricVolume g₁ μ₁) (hμ₂ : IsMetricVolume g₂ μ₂)
    (hEnergy : PatchEnergyEqual g₁ g₂ μ₁ μ₂ Γ) :
    ∃ Φ : M ≃ₘ⟮𝓡∂ n, 𝓡∂ n⟯ M, FixesPatch Γ Φ ∧ PullbackMetric g₁ g₂ Φ := by
  cases n with
  | zero => omega
  | succ m =>
      have hm : 2 ≤ m := by omega
      have hBoundary : ((𝓡∂ (m+1)).boundary M).Nonempty := by
        obtain ⟨p,_⟩ := hΓne
        exact ⟨p,p.property⟩
      let d₁ : DirichletData m M := ⟨g₁,μ₁,hμ₁,hBoundary⟩
      let d₂ : DirichletData m M := ⟨g₂,μ₂,hμ₂,d₁.boundary_nonempty⟩
      obtain ⟨C⟩ := exists_attached_commonCap_of_patchEnergy hm d₁ d₂ hΓ hΓne hEnergy
      obtain ⟨S⟩ := C.exists_signedInteriorCharts
      obtain ⟨ν₁,hν₁⟩ := exists_metricVolume_of_metricVolume g₁ C.firstMetric μ₁ hμ₁
      obtain ⟨ν₂,hν₂⟩ := exists_metricVolume_of_metricVolume g₂ C.secondMetric μ₂ hμ₂
      let D₁ := C.firstData ν₁ hν₁
      let D₂ := C.secondData ν₂ hν₂
      let A₁ := S.firstMetricChart ν₁ hν₁
      let A₂ := S.secondMetricChart ν₂ hν₂
      let W := signedCap C.signedHeight
      have hW : IsOpen W := C.isOpen_signedCap
      have hW₁ : W ⊆ A₁.chart.target := by
        change W ⊆ S.first.target
        rw [S.first_target]
      have hW₂ : W ⊆ A₂.chart.target := by
        change W ⊆ S.second.target
        rw [S.second_target]
      have hMap : MapsTo A₂.chart.symm W C.capMap.source := by
        intro x hx
        change x ∈ signedCap C.signedHeight at hx
        change S.second.symm x ∈ C.capMap.source
        exact S.second_source ▸ S.second.map_target (S.second_target.symm ▸ hx)
      obtain ⟨p,hp⟩ := C.connected_source.nonempty
      let z := S.second p
      have hz : z ∈ signedCap C.signedHeight :=
        S.second_target ▸ S.second.map_source (S.second_source.symm ▸ hp)
      obtain ⟨δ,hδ,hδW⟩ := Metric.mem_nhds_iff.mp (hW.mem_nhds hz)
      let r := δ/2
      have hr : 0 < r := half_pos hδ
      have hBall : closedBall z r ⊆ W := (closedBall_subset_ball (half_lt_self hδ)).trans hδW
      let Q : NativeCapSourceCharts D₁ D₂ C.capMap :=
        NativeCapSourceCharts.of_ball A₁ A₂ hW₁ hW₂ hMap S.same_inverse S.same_field hr hBall
      have hAgree := MeasuredCommonCap.nativeCap_inverse_agreement hEnergy S hν₁ hν₂ Q
      obtain ⟨e,heS,heT,heIso,he⟩ := exists_globalInteriorIsometry_of_capInverseAgreement Q hn
        C.isometry C.target_interior C.source_interior C.connected_source.isPreconnected hAgree
      obtain ⟨Φ,hFix,hΦ⟩ := original_isometry_of_globalInterior_extending_cap C.capMap
        C.firstCopy C.secondCopy heIso heS heT C.source_interior he (C.seam e heS he)
      exact ⟨Φ,fixesPatch_of_patchEnergy_of_fixes_open_subpatch hm d₁ d₂ hΓ C.open_patch
        C.nonempty_patch C.patch_subset hEnergy Φ hΦ hFix,hΦ⟩

end CalderonPatch
