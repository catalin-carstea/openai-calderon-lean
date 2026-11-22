module

public import Proof.CalderonPatch.NormalMetricRealization
public import Proof.CalderonPatch.BoundaryNormalLaplacian

public section

noncomputable section
open Filter Set
open scoped ContDiff Manifold Topology

namespace CalderonPatch

open CalderonN (I X MetricField metricPair pullbackMetric)

variable {n : ℕ} [NeZero n] {M : Type*} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanHalfSpace n) M] [IsManifold (𝓡∂ n) ∞ M]

local notation "J" => 𝓡∂ n
local notation "K" => 𝓘(ℝ, X n)

@[expose] def inwardHalfSpace (n : ℕ) [NeZero n] : Set (X n) := {x | 0 ≤ x (0 : I n)}

@[expose] def positiveHalfSpace (n : ℕ) [NeZero n] : Set (X n) := {x | 0 < x (0 : I n)}

theorem mem_inwardHalfSpace {x : X n} : x ∈ inwardHalfSpace n ↔ 0 ≤ x (0 : I n) := Iff.rfl

theorem mem_positiveHalfSpace {x : X n} : x ∈ positiveHalfSpace n ↔ 0 < x (0 : I n) := Iff.rfl

theorem positiveHalfSpace_subset_inwardHalfSpace : positiveHalfSpace n ⊆ inwardHalfSpace n :=
  fun _ hx => (mem_inwardHalfSpace).mpr ((mem_positiveHalfSpace).mp hx).le

theorem isOpen_positiveHalfSpace : IsOpen (positiveHalfSpace n) :=
  isOpen_lt continuous_const (EuclideanSpace.proj (𝕜 := ℝ) (0 : I n)).continuous

/-- An actual boundary normal chart, with the signed normalized
metric in the orthonormal ambient coordinates. -/
structure NativeBoundaryMetricChart (g : SmoothMetric n M) (p : M) where
  coord : PartialEquiv M (X n)
  open_source : IsOpen coord.source
  ambient : Set (X n)
  open_ambient : IsOpen ambient
  target_eq : coord.target = ambient ∩ inwardHalfSpace n
  point_source : p ∈ coord.source
  point_face : coord p 0 = 0
  smooth : ContMDiffOn J K ∞ coord coord.source
  smooth_inverse : ContMDiffOn K J ∞ coord.symm coord.target
  interior_iff : ∀ x ∈ coord.source, x ∈ (J).interior M ↔ coord x ∈ positiveHalfSpace n
  field : MetricField n
  smooth_field : CalderonN.SmoothMetric ambient field
  normal_field : HasNormalMetricBlock 0 field ambient
  realizes : ∀ x ∈ coord.source, ∀ v w : TangentSpace J x,
    g.inner x v w = metricPair field (coord x) (mfderiv J K coord x v) (mfderiv J K coord x w)

/-- Construct the native metric chart together with the product chart
and normal-coordinate map that share the original face parametrization. -/
theorem exists_nativeBoundaryMetricChart_with_product
    (g : SmoothMetric n M) (p : M) (hp : p ∈ (J).boundary M) :
    ∃ (D : ProductBoundaryChart (n := n) (M := M) (Z := boundaryTangentPlane (0 : I n)))
      (e : OpenPartialHomeomorph (X n) (X n)) (A : NativeBoundaryMetricChart g p),
      p ∈ D.coord.source ∧ (D.coord p).2 = 0 ∧
      D.ambient = inwardChartSplit.symm ⁻¹' e.source ∧
      D.coord.source = (extChartAt J p).source ∩ (extChartAt J p) ⁻¹' e.target ∧
      EqOn e id (e.source ∩ {x | x (0 : I n) = 0}) ∧
      (D.coord : M → boundaryTangentPlane (0 : I n) × ℝ) = inwardChartSplit ∘ e.symm ∘ extChartAt J p ∧
      A.coord.source = D.coord.source ∧ A.ambient = inwardChartSplit ⁻¹' D.ambient ∧
      (A.coord : M → X n) = inwardChartSplit.symm ∘ D.coord ∧
      (A.coord.symm : X n → M) = D.coord.symm ∘ inwardChartSplit := by
  obtain ⟨D,G,e,hpD,hp0,hAmb,hSrc,hE,hEi,hFace,hCoord,_,hG,hSmooth,hBlock⟩ :=
    exists_nativeBoundaryNormalChart g p hp
  let L := inwardChartSplit (n := n)
  let c := D.coord.transEquiv L.symm.toEquiv
  have hcS : c.source = D.coord.source := rfl
  have hcT : c.target = e.source ∩ inwardHalfSpace n := by
    change L ⁻¹' D.coord.target = _
    rw [D.target_eq, preimage_inter, hAmb, ← preimage_comp]
    have hId : (L.symm : _ → X n) ∘ L = id := funext L.symm_apply_apply
    rw [hId, preimage_id]
    congr 1
    ext x
    change (True ∧ 0 ≤ (L x).2) ↔ 0 ≤ x 0
    rw [inwardChartSplit_height, true_and]
  have hcApply : (c : M → X n) = e.symm ∘ extChartAt J p := by
    change L.symm ∘ D.coord = _
    rw [hCoord]
    funext x
    exact L.symm_apply_apply _
  have hcI : ∀ x ∈ c.source, x ∈ (J).interior M ↔ c x ∈ positiveHalfSpace n := by
    intro x hx
    have h := D.interior_iff x hx
    have hL := inwardChartSplit_height (L.symm (D.coord x))
    change (L (L.symm (D.coord x))).2 = _ at hL
    rw [L.apply_symm_apply] at hL
    change _ ↔ 0 < L.symm (D.coord x) 0
    rwa [← hL]
  have hP : c p 0 = 0 := by
    have hL := inwardChartSplit_height (L.symm (D.coord p))
    change (L (L.symm (D.coord p))).2 = _ at hL
    rwa [L.apply_symm_apply, hp0, eq_comm] at hL
  have hC : ContMDiffOn J K ∞ c c.source := L.symm.contDiff.contMDiff.comp_contMDiffOn D.smooth
  have hCi : ContMDiffOn K J ∞ c.symm c.target :=
    D.smooth_inverse.comp L.contDiff.contMDiff.contMDiffOn (fun _ hx => hx)
  have hN : HasNormalMetricBlock 0 (pullbackMetric G e) e.source := by
    intro x hx j
    by_cases h : j = 0
    · subst j
      simpa only [ite_true] using (hBlock x hx).1
    · have hn : (0 : I n) ≠ j := fun he => h he.symm
      rw [ite_eq_right hn]
      exact (hBlock x hx).2 j h
  have hReal : ∀ x ∈ c.source, ∀ v w : TangentSpace J x,
      g.inner x v w = metricPair (pullbackMetric G e) (c x)
        (mfderiv J K (c : M → X n) x v) (mfderiv J K (c : M → X n) x w) := by
    intro x hx v w
    have hx' := (Set.ext_iff.mp hSrc x).mp (show x ∈ D.coord.source from hx)
    have hy : (extChartAt J p) x ∈ e.target := hx'.2
    have hHalf : 0 ≤ (extChartAt J p) x 0 := by
      have hh := extChartAt_target_subset_range p ((extChartAt J p).map_source hx'.1)
      have hR : range ((J) : EuclideanHalfSpace n → X n) = {y | 0 ≤ y (0 : I n)} :=
        range_euclideanHalfSpace n
      exact (Set.ext_iff.mp hR ((extChartAt J p) x)).mp hh
    have hEq := hG ⟨hy,hHalf⟩
    rw [hcApply]
    exact normalMetric_represents_native g p x hE hEi hx'.1 hy hEq v w
  let A : NativeBoundaryMetricChart g p :=
    ⟨c,D.open_source,e.source,e.open_source,hcT,hpD,hP,hC,hCi,hcI,pullbackMetric G e,hSmooth,hN,hReal⟩
  refine ⟨D,e,A,hpD,hp0,hAmb,hSrc,hFace,hCoord,hcS,?_,rfl,rfl⟩
  change e.source = L ⁻¹' D.ambient
  rw [hAmb,preimage_preimage]
  ext z
  exact (show z ∈ e.source ↔ L.symm (L z) ∈ e.source from by rw [L.symm_apply_apply])

/-- Every boundary point has the normalized native chart needed for
the boundary completion of an interior isometry. -/
theorem exists_nativeBoundaryMetricChart (g : SmoothMetric n M) (p : M) (hp : p ∈ (J).boundary M) :
    Nonempty (NativeBoundaryMetricChart g p) := by
  obtain ⟨_,_,A,_⟩ := exists_nativeBoundaryMetricChart_with_product g p hp
  exact ⟨A⟩

end CalderonPatch
