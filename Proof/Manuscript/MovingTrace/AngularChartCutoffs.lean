module

public import Proof.Manuscript.CompactAngularFourier
public import Proof.Manuscript.MovingTrace.StereographicPolarCollar
public import Mathlib.Analysis.Normed.Module.Connected
public import Mathlib.Geometry.Manifold.PartitionOfUnity
public import Mathlib.Analysis.Calculus.ContDiff.Operations

@[expose] public section

noncomputable section
set_option maxHeartbeats 2300000
set_option backward.isDefEq.respectTransparency false

open CalderonN Set Filter Metric
open scoped ContDiff Topology

namespace CalderonPaper

variable {d : ℕ} [Fact (Module.finrank ℝ (X d) = d - 1 + 1)]
abbrev StandardAngularSphere (dim : ℕ) := ↥(standardSphere dim)
local notation "S" => StandardAngularSphere d
local notation "E" => AngularCoordinates d

abbrev angularChartSupport (v : S) (f : X d → ℂ) : Set E :=
  (stereographic' (d-1) v) '' angularSupport f

theorem angularPoint_mem_standardSphere (v : S) (x : E) :
    angularPoint v x ∈ standardSphere d := ((stereographic' (d-1) v).symm x).property

theorem angularChartSupport_isCompact (v : S) (f : X d → ℂ)
    (hf : angularSupport f ⊆ (stereographic' (d-1) v).source) :
    IsCompact (angularChartSupport v f) := by
  haveI : CompactSpace ↥(standardSphere d) :=
    isCompact_iff_compactSpace.mp (isCompact_sphere (0:X d) 1)
  have hClosed : IsClosed (angularSupport f) := isClosed_closure
  exact hClosed.isCompact.image_of_continuousOn
    ((stereographic' (d-1) v).continuousOn.mono hf)

theorem angularDatum_zero_outside_chartSupport (v : S) (f : X d → ℂ)
    {x : E} (hx : x ∉ angularChartSupport v f) : f (angularPoint v x) = 0 := by
  by_contra h
  apply hx
  let κ := stereographic' (d-1) v
  have htarget : x ∈ κ.target := by rw [show κ.target = univ from stereographic'_target v]; exact mem_univ _
  exact ⟨κ.symm x,subset_closure h,κ.right_inv htarget⟩

theorem compactSmooth_angularDatum (v : S) {η u : X d → ℂ}
    (hη : smoothNear η (standardSphere d)) (hu : smoothNear u (standardSphere d))
    (hηS : angularSupport η ⊆ (stereographic' (d-1) v).source) :
    ContDiff ℝ ∞ (fun x => η (angularPoint v x) * u (angularPoint v x)) ∧
      HasCompactSupport (fun x => η (angularPoint v x) * u (angularPoint v x)) := by
  obtain ⟨V,hV,hSV,hηV⟩ := hη
  obtain ⟨W,hW,hSW,huW⟩ := hu
  have h₁ : ContDiff ℝ ∞ (η ∘ angularPoint v) := by
    apply contDiffOn_univ.mp
    exact hηV.comp (angularPoint_contDiff v).contDiffOn (fun x _ => hSV (angularPoint_mem_standardSphere v x))
  have h₂ : ContDiff ℝ ∞ (u ∘ angularPoint v) := by
    apply contDiffOn_univ.mp
    exact huW.comp (angularPoint_contDiff v).contDiffOn (fun x _ => hSW (angularPoint_mem_standardSphere v x))
  refine ⟨h₁.mul h₂,(angularChartSupport_isCompact v η hηS).of_isClosed_subset isClosed_closure ?_⟩
  apply closure_minimal _ (angularChartSupport_isCompact v η hηS).isClosed
  intro x hx
  by_contra h
  exact hx (by simp [angularDatum_zero_outside_chartSupport v η h])

theorem disjoint_angularSupport_common_chart
    (hd : 2 ≤ d) (χ η : X d → ℂ) (hχ : (angularSupport χ).Nonempty)
    (hη : (angularSupport η).Nonempty) (hDis : Disjoint (angularSupport χ) (angularSupport η)) :
    ∃ v : S, angularSupport χ ⊆ (stereographic' (d-1) v).source ∧
      angularSupport η ⊆ (stereographic' (d-1) v).source := by
  have hrank : 1 < Module.rank ℝ (X d) := by
    rw [← Module.finrank_eq_rank,finrank_euclideanSpace_fin]
    exact_mod_cast (show 1 < d by omega)
  let P : Set S := angularSupport χ
  let Q : Set S := angularSupport η
  have hC : IsPreconnected (univ : Set S) := by
    haveI : ConnectedSpace S := isConnected_iff_connectedSpace.mp (isConnected_sphere hrank (0:X d) zero_le_one)
    exact isPreconnected_univ
  have hOut : (P ∪ Q)ᶜ.Nonempty := by
    by_contra h
    have hCov : P ∪ Q = univ := compl_empty_iff.mp (not_nonempty_iff_eq_empty.mp h)
    have hP : IsOpen P := by
      have he : P = Qᶜ := by
        ext w
        constructor
        · exact fun hw => hDis.subset_compl_right hw
        · intro hw
          have hz : w ∈ P ∪ Q := hCov ▸ mem_univ w
          exact hz.resolve_right hw
      exact he ▸ isClosed_closure.isOpen_compl
    have hQ : IsOpen Q := by
      have he : Q = Pᶜ := by
        ext w
        constructor
        · exact fun hw => hDis.subset_compl_left hw
        · intro hw
          have hz : w ∈ P ∪ Q := hCov ▸ mem_univ w
          exact hz.resolve_left hw
      exact he ▸ isClosed_closure.isOpen_compl
    have hLeft : (univ : Set S) ⊆ P := hC.subset_left_of_subset_union hP hQ hDis
      (subset_of_eq hCov.symm) (by
        rw [univ_inter]
        change (angularSupport χ).Nonempty
        exact hχ)
    obtain ⟨z,hz⟩ := hη
    exact (Set.disjoint_left.mp hDis) (hLeft (mem_univ z)) hz
  obtain ⟨v,hv⟩ := hOut
  refine ⟨v,?_,?_⟩
  · rw [stereographic'_source]
    intro z hz h
    exact hv (mem_union_left Q (mem_singleton_iff.mp h ▸ hz))
  · rw [stereographic'_source]
    intro z hz h
    exact hv (mem_union_right P (mem_singleton_iff.mp h ▸ hz))

/-- The input cutoff may be surrounded by a smooth compact angular
amplitude, chosen to avoid a disjoint compact output support. -/
theorem exists_localizingAngularBump {K L : Set E} (hK : IsCompact K) (hL : IsClosed L)
    (hDis : Disjoint K L) :
    ∃ ζ : E → ℝ, ContDiff ℝ ∞ ζ ∧ HasCompactSupport ζ ∧ EqOn ζ 1 K ∧
      Disjoint (tsupport ζ) L := by
  obtain ⟨U,hU,hKU,hUL,hCU⟩ := exists_open_between_and_isCompact_closure hK hL.isOpen_compl
    hDis.subset_compl_right
  obtain ⟨ζ,hζ,_,hS,hone⟩ := exists_contDiff_support_eq_eq_one_iff (n := ⊤) hU hK.isClosed hKU
  refine ⟨ζ,hζ,?_,fun x hx => (hone x).mp hx,?_⟩
  · simpa only [HasCompactSupport,tsupport,hS] using hCU
  · rw [tsupport,hS,Set.disjoint_left]
    exact fun _ hh hx => hUL hh hx

end CalderonPaper
