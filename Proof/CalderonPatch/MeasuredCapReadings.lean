module

public import Proof.CalderonPatch.MeasuredCapBox
public import Proof.CalderonPatch.CapScalarReading

import Mathlib.Tactic

public section
noncomputable section
open Filter Metric Set
open scoped ContDiff Manifold Topology

namespace CalderonPatch

open CalderonN (I X)

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace (n+1)) M] [IsManifold (𝓡∂ (n+1)) ∞ M]
  [MeasurableSpace M]

local notation "N" => (n+1)
local notation "E" => X N
local notation "Zt" => boundaryTangentPlane (0 : I N)
local notation "L" => (inwardChartSplit (n := N))
local notation "J" => 𝓡∂ N
local notation "R" => 𝓘(ℝ, ℝ)
local notation "H" => inwardHalfSpace N

variable {d₁ d₂ : DirichletData n M} {Γ : Set ((𝓡∂ (n+1)).boundary M)}

namespace MeasuredCommonCap

variable (C : MeasuredCommonCap d₁ d₂ Γ)

abbrev productFirst : ProductBoundaryChart (n := N) (M := M) (Z := Zt) :=
  C.charts.prod₁.restrictAmbient C.open_ambient C.subset_first

abbrev productSecond : ProductBoundaryChart (n := N) (M := M) (Z := Zt) :=
  C.charts.prod₂.restrictAmbient C.open_ambient C.subset_second

abbrev pushedPoint (x : E) : Zt × ℝ := C.coordinates.push (L x)

theorem pushedPoint_height_nonneg_iff (x : E) :
    0 ≤ (C.pushedPoint x).2 ↔ -C.signedHeight (normalTangentialCoordinates x) ≤ x 0 := by
  let z := (L x).1
  let t := (L x).2
  have h₁ : (C.coordinates.push (z,-C.coordinates.height z)).2 = 0 :=
    congrArg Prod.snd (C.coordinates.push_boundary z)
  have he : C.pushedPoint x = C.coordinates.push (z,t) := rfl
  rw [he,C.signedHeight_read,← inwardChartSplit_height x,← h₁]
  exact (C.coordinates.push_monotone z).le_iff_le

theorem pushedPoint_height_eq_zero (x : E)
    (hx : x 0 = -C.signedHeight (normalTangentialCoordinates x)) :
    (C.pushedPoint x).2 = 0 := by
  have hc : (L x).2 = -C.coordinates.height (L x).1 :=
    (inwardChartSplit_height x).trans (hx.trans (congrArg Neg.neg (C.signedHeight_read x)))
  have he : L x = ((L x).1,-C.coordinates.height (L x).1) := Prod.ext rfl hc
  change (C.coordinates.push (L x)).2 = 0
  rw [he,C.coordinates.push_boundary]

theorem pushedPoint_height_nonneg_of_inward {x : E} (hx : x ∈ H) :
    0 ≤ (C.pushedPoint x).2 :=
  (C.pushedPoint_height_nonneg_iff x).mpr <|
    (neg_nonpos.mpr (C.signedHeight_bounds _).1).trans hx

theorem chartInverse_first {x : E} (hx : x ∈ C.signedRegion ∩ H) :
    C.charts.first.coord.symm x = C.productFirst.coord.symm (L x) :=
  nativeInverse_eq_productInverse C.charts.first C.charts.source₁ C.charts.coord₁
    C.open_ambient C.subset_first hx

theorem chartInverse_second {x : E} (hx : x ∈ C.signedRegion ∩ H) :
    C.charts.second.coord.symm x = C.productSecond.coord.symm (L x) :=
  nativeInverse_eq_productInverse C.charts.second C.charts.source₂ C.charts.coord₂
    C.open_ambient C.subset_second hx

theorem nativeAmbient_first : C.signedRegion ⊆ C.charts.first.ambient :=
  C.subset_signed.trans C.charts.signed₁

theorem nativeAmbient_second : C.signedRegion ⊆ C.charts.second.ambient :=
  C.subset_signed.trans C.charts.signed₂

theorem nativeFaceInverse_eq {x : E} (hx : x ∈ C.signedRegion) (hx₀ : x 0 = 0) :
    C.charts.first.coord.symm x = C.charts.second.coord.symm x :=
  C.charts.common_inverse ⟨C.subset_signed hx,hx₀⟩

/-- Signed scalar representatives on a single neighborhood containing
the entire coordinate box, in both cap extensions. -/
structure ScalarReadings (w₁ w₂ : M → ℝ) where
  domain : Set E
  open_domain : IsOpen domain
  box_subset : C.signedBox ⊆ domain
  domain_subset : domain ⊆ C.signedRegion
  first : E → ℝ
  second : E → ℝ
  smooth_first : ContDiff ℝ ∞ first
  smooth_second : ContDiff ℝ ∞ second
  reads_first : EqOn first (w₁ ∘ C.productFirst.coord.symm ∘ C.coordinates.push ∘ L)
    (domain ∩ {x | 0 ≤ (C.pushedPoint x).2})
  reads_second : EqOn second (w₂ ∘ C.productSecond.coord.symm ∘ C.coordinates.push ∘ L)
    (domain ∩ {x | 0 ≤ (C.pushedPoint x).2})

theorem exists_scalarReadings {w₁ w₂ : M → ℝ}
    (hw₁ : ContMDiff J R ∞ w₁) (hw₂ : ContMDiff J R ∞ w₂) :
    Nonempty (C.ScalarReadings w₁ w₂) := by
  obtain ⟨r₁,U₁,hr₁,hU₁,hBU₁,hU₁W,hR₁⟩ := C.coordinates.first.exists_signed_scalar_reading
    C.coordinates.smooth_push hw₁ C.isCompact_signedBox C.signedBox_subset
  obtain ⟨r₂,U₂,hr₂,hU₂,hBU₂,hU₂W,hR₂⟩ := C.coordinates.second.exists_signed_scalar_reading
    C.coordinates.smooth_push hw₂ C.isCompact_signedBox C.signedBox_subset
  exact ⟨⟨U₁ ∩ U₂,hU₁.inter hU₂,fun x hx => ⟨hBU₁ hx,hBU₂ hx⟩,
    fun _ hx => hU₁W hx.1,r₁,r₂,hr₁,hr₂,
    fun _ hx => hR₁ ⟨hx.1.1,hx.2⟩,fun _ hx => hR₂ ⟨hx.1.2,hx.2⟩⟩⟩

variable {C} {w₁ w₂ : M → ℝ} (D : C.ScalarReadings w₁ w₂)

theorem ScalarReadings.original_first :
    EqOn ((w₁ ∘ C.firstCopy.embed) ∘ C.charts.first.coord.symm) D.first (D.domain ∩ H) := by
  intro x hx
  change w₁ (C.firstCopy.embed (C.charts.first.coord.symm x)) = D.first x
  rw [C.chartInverse_first ⟨D.domain_subset hx.1,hx.2⟩,
    C.coordinates.first.original_scalar_eq (w := w₁) (D.domain_subset hx.1) hx.2]
  exact (D.reads_first ⟨hx.1,C.pushedPoint_height_nonneg_of_inward hx.2⟩).symm

theorem ScalarReadings.original_second :
    EqOn ((w₂ ∘ C.secondCopy.embed) ∘ C.charts.second.coord.symm) D.second (D.domain ∩ H) := by
  intro x hx
  change w₂ (C.secondCopy.embed (C.charts.second.coord.symm x)) = D.second x
  rw [C.chartInverse_second ⟨D.domain_subset hx.1,hx.2⟩,
    C.coordinates.second.original_scalar_eq (w := w₂) (D.domain_subset hx.1) hx.2]
  exact (D.reads_second ⟨hx.1,C.pushedPoint_height_nonneg_of_inward hx.2⟩).symm

theorem ScalarReadings.sub_zero_on_graph
    (hw₁ : EqOn w₁ 0 ((J).boundary M)) (hw₂ : EqOn w₂ 0 ((J).boundary M))
    {x : E} (hx : x ∈ D.domain) (hx₀ : x 0 = -C.signedHeight (normalTangentialCoordinates x)) :
    (D.first - D.second) x = 0 := by
  have ht := C.pushedPoint_height_eq_zero x hx₀
  have h₁ : D.first x = w₁ (C.productFirst.coord.symm (C.pushedPoint x)) :=
    D.reads_first ⟨hx,ht.ge⟩
  have h₂ : D.second x = w₂ (C.productSecond.coord.symm (C.pushedPoint x)) :=
    D.reads_second ⟨hx,ht.ge⟩
  change D.first x - D.second x = 0
  rw [h₁,h₂,C.coordinates.first.scalar_zero_on_graph hw₁ (D.domain_subset hx) ht,
    C.coordinates.second.scalar_zero_on_graph hw₂ (D.domain_subset hx) ht,sub_zero]

end MeasuredCommonCap

end CalderonPatch
