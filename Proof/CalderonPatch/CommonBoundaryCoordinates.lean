module

public import Proof.CalderonPatch.NativeBoundaryMetricChart

public section

noncomputable section
open Filter Set
open scoped ContDiff Manifold Topology

namespace CalderonPatch

open CalderonN (I X)

variable {n : ℕ} [NeZero n] {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace n) M] [IsManifold (𝓡∂ n) ∞ M]

local notation "J" => 𝓡∂ n
local notation "Zt" => boundaryTangentPlane (0 : I n)

/-- The chart's inward height is zero at original boundary points. -/
theorem ProductBoundaryChart.height_eq_zero_on_boundary
    {Z : Type} [NormedAddCommGroup Z] [InnerProductSpace ℝ Z] [FiniteDimensional ℝ Z]
    (D : ProductBoundaryChart (n := n) (M := M) (Z := Z)) {p : M}
    (hp : p ∈ (J).boundary M) (hD : p ∈ D.coord.source) : (D.coord p).2 = 0 := by
  have hnonneg : 0 ≤ (D.coord p).2 :=
    (D.target_eq ▸ D.coord.map_source hD : _ ∈ D.ambient ∩ (univ ×ˢ Ici (0 : ℝ))).2.2
  apply le_antisymm _ hnonneg
  apply le_of_not_gt
  have h : p ∈ ((J).interior M)ᶜ := by rw [(J).compl_interior]; exact hp
  exact fun hpos => h ((D.interior_iff p hD).mpr hpos)

/-- Normal coordinates based on one native chart have its unchanged
boundary parametrization. -/
theorem normalChart_eq_original_on_boundary (p : M)
    (D : ProductBoundaryChart (n := n) (M := M) (Z := Zt))
    (e : OpenPartialHomeomorph (X n) (X n))
    (hSrc : D.coord.source = (extChartAt J p).source ∩ (extChartAt J p) ⁻¹' e.target)
    (hFace : EqOn e id (e.source ∩ {x | x (0 : I n) = 0}))
    (hCoord : (⇑D.coord : M → Zt × ℝ) = inwardChartSplit ∘ e.symm ∘ extChartAt J p)
    {q : M} (hq : q ∈ (J).boundary M) (hD : q ∈ D.coord.source) :
    D.coord q = inwardChartSplit (extChartAt J p q) := by
  let x := extChartAt J p q
  have hx : x ∈ e.target := (hSrc ▸ hD :
    q ∈ (extChartAt J p).source ∩ (extChartAt J p) ⁻¹' e.target).2
  have h := D.height_eq_zero_on_boundary hq hD
  rw [hCoord] at h ⊢
  change (inwardChartSplit (e.symm x)).2 = 0 at h
  rw [inwardChartSplit_height] at h
  have he : e (e.symm x) = e.symm x := hFace ⟨e.map_target hx,h⟩
  rw [e.right_inv hx] at he
  exact congrArg inwardChartSplit he.symm

/-- Two charts with a shared boundary parametrization can be restricted
to a single ambient neighborhood whose boundary footprint lies in the
measured patch. -/
theorem exists_commonBoundaryNeighborhood
    (D₁ D₂ : ProductBoundaryChart (n := n) (M := M) (Z := Zt))
    {p : (J).boundary M} (hp₁ : (p : M) ∈ D₁.coord.source) (hp₂ : (p : M) ∈ D₂.coord.source)
    {Γ : Set ((J).boundary M)} (hΓ : IsOpen Γ) (hpΓ : p ∈ Γ)
    (hSame : ∀ q : (J).boundary M, (q : M) ∈ D₁.coord.source → (q : M) ∈ D₂.coord.source →
      D₁.coord q = D₂.coord q) :
    ∃ W : Set (Zt × ℝ), IsOpen W ∧ D₂.coord p ∈ W ∧ W ⊆ D₁.ambient ∧ W ⊆ D₂.ambient ∧
      ∀ q : (J).boundary M, (q : M) ∈ D₂.coord.source → D₂.coord q ∈ W →
        (q : M) ∈ D₁.coord.source ∧ D₁.coord q = D₂.coord q ∧ q ∈ Γ := by
  obtain ⟨V,hV,hVΓ⟩ := isOpen_induced_iff.mp hΓ
  have hpV : (p : M) ∈ V := by
    change p ∈ Subtype.val ⁻¹' V
    rwa [hVΓ]
  let x := D₂.coord p
  have hx₂ : x ∈ D₂.coord.target := D₂.coord.map_source hp₂
  have hx₁ : x ∈ D₁.coord.target := by
    change D₂.coord p ∈ D₁.coord.target
    rw [← hSame p hp₁ hp₂]
    exact D₁.coord.map_source hp₁
  have hxA₁ : x ∈ D₁.ambient := (D₁.target_eq ▸ hx₁ : x ∈ D₁.ambient ∩ _).1
  have hxA₂ : x ∈ D₂.ambient := (D₂.target_eq ▸ hx₂ : x ∈ D₂.ambient ∩ _).1
  have hin : D₂.coord.symm x ∈ D₁.coord.source ∩ V := by
    change D₂.coord.symm (D₂.coord p) ∈ _
    rw [D₂.coord.left_inv hp₂]
    exact ⟨hp₁,hpV⟩
  have hEvent : ∀ᶠ y in 𝓝[D₂.coord.target] x, D₂.coord.symm y ∈ D₁.coord.source ∩ V :=
    (D₂.smooth_inverse.continuousOn x hx₂).tendsto ((D₁.open_source.inter hV).mem_nhds hin)
  obtain ⟨U,hUok,hU,hxU⟩ := _root_.eventually_nhds_iff.mp (eventually_nhdsWithin_iff.mp hEvent)
  let W := (U ∩ D₁.ambient) ∩ D₂.ambient
  refine ⟨W,(hU.inter D₁.open_ambient).inter D₂.open_ambient,⟨⟨hxU,hxA₁⟩,hxA₂⟩,
    (fun _ hy => hy.1.2),inter_subset_right,?_⟩
  intro q hq hqW
  have h := hUok _ hqW.1.1 (D₂.coord.map_source hq)
  rw [D₂.coord.left_inv hq] at h
  exact ⟨h.1,hSame q h.1 hq,hVΓ ▸ h.2⟩

/-- A common collar neighborhood can be chosen to have measured
boundary footprints on both sides. -/
theorem exists_pairedBoundaryNeighborhood
    (D₁ D₂ : ProductBoundaryChart (n := n) (M := M) (Z := Zt))
    {p : (J).boundary M} (hp₁ : (p : M) ∈ D₁.coord.source) (hp₂ : (p : M) ∈ D₂.coord.source)
    {Γ : Set ((J).boundary M)} (hΓ : IsOpen Γ) (hpΓ : p ∈ Γ)
    (hSame : ∀ q : (J).boundary M, (q : M) ∈ D₁.coord.source → (q : M) ∈ D₂.coord.source →
      D₁.coord q = D₂.coord q) :
    ∃ W : Set (Zt × ℝ), IsOpen W ∧ D₂.coord p ∈ W ∧ W ⊆ D₁.ambient ∧ W ⊆ D₂.ambient ∧
      (∀ q : (J).boundary M, (q : M) ∈ D₁.coord.source → D₁.coord q ∈ W → q ∈ Γ) ∧
      (∀ q : (J).boundary M, (q : M) ∈ D₂.coord.source → D₂.coord q ∈ W →
        (q : M) ∈ D₁.coord.source ∧ D₁.coord q = D₂.coord q ∧ q ∈ Γ) := by
  obtain ⟨U,hU,hpU,hU₁,hU₂,hIn⟩ := exists_commonBoundaryNeighborhood D₁ D₂ hp₁ hp₂ hΓ hpΓ hSame
  obtain ⟨V,hV,hpV,_,_,hOut⟩ := exists_commonBoundaryNeighborhood D₂ D₁ hp₂ hp₁ hΓ hpΓ
    (fun q h₂ h₁ => (hSame q h₁ h₂).symm)
  have hpV' : D₂.coord p ∈ V := hSame p hp₁ hp₂ ▸ hpV
  refine ⟨U ∩ V,hU.inter hV,⟨hpU,hpV'⟩,inter_subset_left.trans hU₁,inter_subset_left.trans hU₂,?_,?_⟩
  · exact fun q hq hqV => (hOut q hq hqV.2).2.2
  · exact fun q hq hqU => hIn q hq hqU.1

end CalderonPatch
