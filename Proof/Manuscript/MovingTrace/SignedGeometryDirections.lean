module

public import Proof.Manuscript.MovingTrace.ActualRadialVelocityModel
public import Proof.Manuscript.RadiusReorderedAngular
public import Proof.Manuscript.RadiusAngularAnnularBounds
public import Mathlib.Analysis.Calculus.ContDiff.Operations

@[expose] public section

noncomputable section
set_option maxHeartbeats 2600000
set_option backward.isDefEq.respectTransparency false

open CalderonN Set Metric Filter
open scoped ContDiff Topology

namespace CalderonPaper

variable {n : ℕ}
local notation "dim" => n+1
local notation "Z" => X dim
local notation "P" => MovingSymbolGeometry dim

/-- Keep the metric member, center, and radius slope fixed while moving
along the entire signed auxiliary interval. -/
theorem signedGeometryCompact_radius_line_mem {Y : Set Z} {ρ B δ : ℝ}
    {p : P} (hp : p ∈ movingSymbolGeometryCompact Y ρ B) {r : ℝ} (hr : r ∈ Icc (-δ) ρ) :
    movingSymbolSignedRadiusEquiv dim (((movingSymbolSignedRadiusEquiv dim).symm p).1,r) ∈
      signedGeometryCompact Y ρ B δ := by
  rcases p with ⟨⟨lam,y,s⟩,b⟩
  exact ⟨(((lam,y),b),r),⟨⟨⟨hp.1.1,hp.1.2.1⟩,hp.2⟩,hr⟩,rfl⟩

/-- The signed Taylor neighborhood includes a two-sided germ at zero. -/
theorem signedGeometryCompact_eventually_radius_mem {Y : Set Z} {ρ B δ : ℝ}
    (hδ : 0 < δ) (hρ : 0 < ρ) {p : P} (hp : p ∈ movingSymbolGeometryCompact Y ρ B) :
    ∀ᶠ r : ℝ in 𝓝 0,
      movingSymbolSignedRadiusEquiv dim (((movingSymbolSignedRadiusEquiv dim).symm p).1,r) ∈
        signedGeometryCompact Y ρ B δ := by
  filter_upwards [Icc_mem_nhds (neg_neg_of_pos hδ) hρ] with r hr
  exact signedGeometryCompact_radius_line_mem hp hr

/-- An unsigned physical geometry has its complete radius segment inside
every open set that contains the signed auxiliary compact. -/
theorem movingSymbolGeometryCompact_subset_radiusSegment {Y : Set Z} {ρ B δ : ℝ} {U : Set P}
    (hδ : 0 ≤ δ) (hJU : signedGeometryCompact Y ρ B δ ⊆ U) :
    movingSymbolGeometryCompact Y ρ B ⊆ geometryRadiusSegment (movingSymbolSignedRadiusEquiv dim) U := by
  intro p hp t ht
  have hr : p.1.2.2 ∈ Icc (0:ℝ) ρ := hp.1.2.2
  have htr : t*p.1.2.2 ∈ Icc (-δ) ρ :=
    ⟨(neg_nonpos.mpr hδ).trans (mul_nonneg ht.1 hr.1),
      (mul_le_of_le_one_left hr.1 ht.2).trans hr.2⟩
  exact hJU (signedGeometryCompact_radius_line_mem hp htr)

end CalderonPaper
