module

public import Proof.CalderonPatch.BoundaryMetric
public import Proof.CalderonPatch.LocalHalfSpaceMetric
public import Proof.CalderonPatch.BoundaryNormalChart

import Mathlib.Analysis.Normed.Module.FiniteDimension
import Proof.CalderonN.LocalChartExtension
import Mathlib.Tactic

public section

noncomputable section
open Filter Matrix Metric Set
open scoped ContDiff Manifold Topology

namespace CalderonPatch

open CalderonN (I X Mat MetricField axis lowerHalfSpace)

variable {n : ℕ}

/-- The tangential vector space of a flat coordinate face. -/
abbrev boundaryTangentPlane (i : I n) : Submodule ℝ (X n) :=
  (EuclideanSpace.proj (𝕜 := ℝ) i).toLinearMap.ker

private theorem boundaryFoot_coordinate_zero (i : I n) (x : X n) : boundaryFoot i x i = 0 := by
  rw [boundaryFoot_apply]
  simp [axis]

private def boundaryLinearSplit (i : I n) : X n →L[ℝ] boundaryTangentPlane i × ℝ :=
  ((boundaryFoot i).codRestrict (boundaryTangentPlane i) (boundaryFoot_coordinate_zero i)).prod
    (-EuclideanSpace.proj i)

/-- Split a flat face into its tangential coordinates and the signed
normal coordinate, using the negative inward sign for the half-space extension. -/
def boundaryChartSplit (i : I n) : X n ≃L[ℝ] boundaryTangentPlane i × ℝ := by
  let A := boundaryLinearSplit i
  have hAxis : axis i i = 1 := by simp [axis]
  have hAij : Function.Injective A := (injective_iff_map_eq_zero A).mpr (fun x hx => by
    have hxcoord := congrArg (fun q : boundaryTangentPlane i × ℝ => q.2) hx
    have hf := congrArg (fun q : boundaryTangentPlane i × ℝ => (q.1 : X n)) hx
    change -x i = 0 at hxcoord
    change boundaryFoot i x = 0 at hf
    rwa [boundaryFoot_on_face _ (neg_eq_zero.mp hxcoord)] at hf)
  have hAs : Function.Surjective A := by
    rintro ⟨z,t⟩
    let x : X n := (z : X n) - t • axis i
    have hz : (z : X n) i = 0 := z.property
    have hxi : x i = -t := by simp [x, hz, hAxis]
    refine ⟨x, Prod.ext (Subtype.ext ?_) ?_⟩
    · change boundaryFoot i x = (z : X n)
      rw [boundaryFoot_apply, hxi]
      change ((z : X n) - t • axis i) - (-t) • axis i = (z : X n)
      rw [neg_smul, sub_neg_eq_add, sub_add_cancel]
    · change -x i = t
      rw [hxi, neg_neg]
  exact ContinuousLinearEquiv.ofBijective A (LinearMap.ker_eq_bot.mpr hAij) (LinearMap.range_eq_top.mpr hAs)

theorem boundaryChartSplit_height (i : I n) (x : X n) : (boundaryChartSplit i x).2 = -x i := by
  unfold boundaryChartSplit boundaryLinearSplit
  rfl

theorem boundaryChartSplit_tangent (i : I n) (x : X n) :
    ((boundaryChartSplit i x).1 : X n) = boundaryFoot i x := by
  unfold boundaryChartSplit boundaryLinearSplit
  rfl

theorem boundaryChartSplit_maps_halfSpace (i : I n) (x : X n) :
    boundaryChartSplit i x ∈ lowerHalfSpace (boundaryTangentPlane i) ↔ 0 ≤ x i := by
  change (True ∧ (boundaryChartSplit i x).2 ≤ 0) ↔ 0 ≤ x i
  rw [boundaryChartSplit_height, true_and, neg_nonpos]

/-- An actual one-sided smooth coordinate metric has a global smooth
positive extension agreeing in a relative neighborhood of the point. -/
theorem exists_global_metric_germ_of_halfSpace {p : X n} {i : I n} (hi : p i = 0)
    {U : Set (X n)} (hU : IsOpen U) (hp : p ∈ U) {g : MetricField n}
    (hg : CalderonN.SmoothMetric (U ∩ {x | 0 ≤ x i}) g) :
    ∃ G : MetricField n, CalderonN.SmoothMetric univ G ∧ G =ᶠ[𝓝[{x | 0 ≤ x i}] p] g := by
  let e := boundaryChartSplit i
  let W := e.symm ⁻¹' U
  let g' : boundaryTangentPlane i × ℝ → Mat n := fun q => g (e.symm q)
  let b := (e p).1
  have hP : (e p).2 = 0 := by change (boundaryChartSplit i p).2 = 0; rw [boundaryChartSplit_height, hi, neg_zero]
  have heP : e p = (b,0) := Prod.ext rfl hP
  have hWP : (b,(0 : ℝ)) ∈ W := by rw [← heP]; change e.symm (e p) ∈ U; rwa [e.symm_apply_apply]
  have hW : IsOpen W := hU.preimage e.symm.continuous
  have hMap : MapsTo e.symm (W ∩ lowerHalfSpace (boundaryTangentPlane i)) (U ∩ {x | 0 ≤ x i}) := by
    intro q hq
    refine ⟨hq.1, (boundaryChartSplit_maps_halfSpace i (e.symm q)).mp ?_⟩
    change e (e.symm q) ∈ lowerHalfSpace (boundaryTangentPlane i)
    rw [e.apply_symm_apply]
    exact hq.2
  obtain ⟨V, G', hV, hVb, _, hG, hPos, hEq⟩ := exists_local_halfSpace_metric_extension
    hW hWP (g := g') (fun j k => (hg.1 j k).comp e.symm.contDiff.contDiffOn hMap)
    (fun q hq => hg.2 _ (hMap hq))
  let V' := e ⁻¹' V
  have hV' : IsOpen V' := hV.preimage e.continuous
  have hVp : p ∈ V' := by change e p ∈ V; rwa [heP]
  let G₀ : MetricField n := G' ∘ e
  have hG₀ : CalderonN.SmoothMetric V' G₀ :=
    ⟨fun j k => ((hG j k).comp e.contDiff).contDiffOn, fun q hq => hPos _ hq⟩
  obtain ⟨G, hG', hGg⟩ := CalderonN.exists_global_chart_metric hV' (isCompact_singleton (x := p))
    (singleton_subset_iff.mpr hVp) hG₀
  refine ⟨G, hG', ?_⟩
  have hre : G =ᶠ[𝓝 p] G₀ := hGg p (mem_singleton p)
  have hNear : ∀ᶠ x in 𝓝 p, x ∈ V' := hV'.mem_nhds hVp
  filter_upwards [hre.filter_mono nhdsWithin_le_nhds, hNear.filter_mono nhdsWithin_le_nhds,
    self_mem_nhdsWithin] with x hx hVx hhalf
  have h := hEq ⟨hVx, (boundaryChartSplit_maps_halfSpace i x).mpr hhalf⟩
  change G' (e x) = g (e.symm (e x)) at h
  rw [e.symm_apply_apply] at h
  exact hx.trans h

variable [NeZero n] {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace n) M]
  [IsManifold (𝓡∂ n) ∞ M]

/-- The protected native metric has a smooth positive extension at
every flat-face point of its canonical boundary chart. -/
theorem exists_global_metric_germ_of_native_boundaryChart (g : SmoothMetric n M) (p : M)
    {x : X n} (hx : x ∈ (extChartAt (𝓡∂ n) p).target) (hx₀ : x 0 = 0) :
    ∃ G : MetricField n, CalderonN.SmoothMetric univ G ∧
      G =ᶠ[𝓝[{y | 0 ≤ y 0}] x] chartMetric g p := by
  have h := extChartAt_target_eventuallyEqSet_of_mem (I := 𝓡∂ n) hx
  have hR : range ((𝓡∂ n) : EuclideanHalfSpace n → X n) = {y | 0 ≤ y 0} := range_euclideanHalfSpace n
  rw [hR] at h
  obtain ⟨U, hEq, hU, hUx⟩ := _root_.eventually_nhds_iff.mp h
  have hSub : U ∩ {y : X n | 0 ≤ y 0} ⊆ (extChartAt (𝓡∂ n) p).target :=
    fun y hy => (hEq y hy.1).mpr hy.2
  have hG := chartMetric_smooth g p
  exact exists_global_metric_germ_of_halfSpace hx₀ hU hUx
    ⟨fun j k => (hG.1 j k).mono hSub, fun y hy => hG.2 y (hSub hy)⟩

end CalderonPatch
