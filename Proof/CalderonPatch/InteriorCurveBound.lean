module

public import Proof.CalderonPatch.InteriorPathLength

@[expose] public section

noncomputable section
open Bundle Filter Manifold MeasureTheory Metric Set
open scoped Bundle ContDiff ENNReal Manifold NNReal Topology

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace normedSpaceTangentSpaceVectorSpace

namespace CalderonPatch

open CalderonN (X)

variable {n : ℕ} [NeZero n] {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace n) M] [IsManifold (𝓡∂ n) ∞ M]

local notation "J" => 𝓡∂ n
local notation "K" => 𝓘(ℝ, X n)
local notation "JR" => 𝓘(ℝ, ℝ)

set_option backward.isDefEq.respectTransparency false in
/-- Close interior points near any point of a manifold with boundary
can be joined by short curves staying in the interior. The chart segment
lies in a convex ball intersected with the interior of the half-space.
This is the two-endpoint form of the local length estimate in mathlib's
`eventually_riemannianEDist_le_edist_extChartAt`. -/
theorem exists_interior_curve_bound (g : SmoothMetric n M) (p : M) :
    ∃ C : ℝ≥0, 0 < C ∧ ∃ V : Set M, IsOpen V ∧ p ∈ V ∧
      ∀ x ∈ V ∩ (𝓡∂ n).interior M, ∀ y ∈ V ∩ (𝓡∂ n).interior M,
        ∃ γ : ℝ → M, ContMDiffOn JR J 1 γ (Icc 0 1) ∧
          γ 0 = x ∧ γ 1 = y ∧ MapsTo γ (Icc 0 1) ((𝓡∂ n).interior M) ∧
          nativePathLength g γ 0 1 ≤ C * edist (extChartAt J p x) (extChartAt J p y) := by
  let _ : RiemannianBundle (fun x : M => TangentSpace J x) := ⟨g.toRiemannianMetric⟩
  let _ : IsContinuousRiemannianBundle (X n) (fun x : M => TangentSpace J x) :=
    ⟨⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩⟩
  let c := extChartAt J p
  obtain ⟨C, hC, hBound⟩ := eventually_enorm_mfderivWithin_symm_extChartAt_lt J p
  let D := c.target ∩ {z | ‖mfderivWithin K J c.symm (range J) z‖ₑ < C}
  have hNear : D ∈ 𝓝[range J] (c p) := by
    apply inter_mem (extChartAt_target_mem_nhdsWithin p)
    exact hBound
  obtain ⟨r, hr, hbD⟩ := Metric.mem_nhdsWithin_iff.mp hNear
  let B := ball (c p) r ∩ interior (range J)
  have hBo : IsOpen B := isOpen_ball.inter isOpen_interior
  have hBD : B ⊆ D := fun _ hx => hbD ⟨hx.1, interior_subset hx.2⟩
  have hConvex : Convex ℝ B := (convex_ball _ _).inter (𝓡∂ n).convex_range.interior
  let V := c.source ∩ c ⁻¹' ball (c p) r
  have hV : IsOpen V := (continuousOn_extChartAt p).isOpen_inter_preimage
    (isOpen_extChartAt_source p) isOpen_ball
  have hpc : p ∈ c.source := mem_extChartAt_source p
  refine ⟨C, hC, V, hV, ⟨hpc, mem_ball_self hr⟩, ?_⟩
  have hMem (x : M) (hx : x ∈ V ∩ (𝓡∂ n).interior M) : c x ∈ B := by
    have hxs : x ∈ (chartAt (EuclideanHalfSpace n) p).source := by
      simpa only [c, extChartAt_source] using (show x ∈ c.source from hx.1.1)
    have h := ((𝓡∂ n).isInteriorPoint_iff_of_mem_atlas (n := ∞) (by simp)
      (chart_mem_atlas _ p) hxs).1 hx.2
    exact ⟨hx.1.2, interior_mono (extChartAt_target_subset_range (I := J) p) h⟩
  intro x hx y hy
  let η := ContinuousAffineMap.lineMap (R := ℝ) (c x) (c y)
  let γ := c.symm ∘ η
  have hη : MapsTo η (Icc 0 1) B := by
    apply image_subset_iff.mp
    rw [ContinuousAffineMap.coe_lineMap_eq, ← segment_eq_image_lineMap]
    exact hConvex.segment_subset (hMem x hx) (hMem y hy)
  have hηD : MapsTo η (Icc 0 1) D := fun _ ht => hBD (hη ht)
  have hη1 : ContMDiffOn JR K 1 η (Icc 0 1) := η.contDiff.contMDiff.contMDiffOn
  have hγ1 : ContMDiffOn JR J 1 γ (Icc 0 1) :=
    (contMDiffOn_extChartAt_symm p).comp hη1 (fun _ ht => (hηD ht).1)
  have hγα : γ 0 = x := by simp [γ, η, ContinuousAffineMap.coe_lineMap_eq, hx.1.1]
  have hγβ : γ 1 = y := by simp [γ, η, ContinuousAffineMap.coe_lineMap_eq, hy.1.1]
  have hγI : MapsTo γ (Icc 0 1) ((𝓡∂ n).interior M) := by
    intro t ht
    have htC := (hηD ht).1
    have hs : c.symm (η t) ∈ (chartAt (EuclideanHalfSpace n) p).source := by
      simpa only [c, extChartAt_source] using c.map_target htC
    apply ((𝓡∂ n).isInteriorPoint_iff_of_mem_atlas (n := ∞) (by simp)
      (chart_mem_atlas _ p) hs).2
    change c (c.symm (η t)) ∈ interior c.target
    rw [c.right_inv htC]
    exact interior_maximal (hBD.trans inter_subset_left) hBo (hη ht)
  refine ⟨γ, hγ1, hγα, hγβ, hγI, ?_⟩
  rw [← pathELength_eq_native g, ← lintegral_fderiv_lineMap_eq_edist,
    pathELength_eq_lintegral_mfderivWithin_Icc, ← lintegral_const_mul' _ _ ENNReal.coe_ne_top]
  apply setLIntegral_mono' measurableSet_Icc
  intro t ht
  have hD : mfderivWithin JR J γ (Icc 0 1) t =
      (mfderivWithin K J c.symm (range J) (η t)).comp (mfderivWithin JR K η (Icc 0 1) t) := by
    apply mfderivWithin_comp
    · exact mdifferentiableWithinAt_extChartAt_symm (hηD ht).1
    · exact hη1.mdifferentiableOn one_ne_zero t ht
    · exact fun _ hx => extChartAt_target_subset_range p (hηD hx).1
    · rw [uniqueMDiffWithinAt_iff_uniqueDiffWithinAt]
      exact uniqueDiffOn_Icc zero_lt_one t ht
  have hD' : mfderivWithin JR J γ (Icc 0 1) t 1 =
      (mfderivWithin K J c.symm (range J) (η t)) (mfderivWithin JR K η (Icc 0 1) t 1) :=
    congrArg (fun D : ℝ →L[ℝ] TangentSpace J (γ t) => D 1) hD
  rw [hD']
  apply (ContinuousLinearMap.le_opENorm _ _).trans
  gcongr
  · exact (hηD ht).2.le
  · simp only [mfderivWithin_eq_fderivWithin]
    exact le_of_eq rfl

end CalderonPatch
