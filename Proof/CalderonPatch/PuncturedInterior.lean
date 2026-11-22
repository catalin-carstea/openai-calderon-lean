module

public import Proof.CalderonPatch.ConnectedInterior

import Mathlib.Analysis.Normed.Module.Connected

public section

open Filter Metric Set
open scoped ContDiff Manifold Topology

namespace CalderonPatch

section Ball

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A punctured centered ball is the continuous image of an open radial
interval times a connected unit sphere. -/
theorem isConnected_puncturedBall (hRank : 1 < Module.rank ℝ E)
    (c : E) {r : ℝ} (hr : 0 < r) : IsConnected (ball c r \ {c}) := by
  let A := Ioo (0 : ℝ) r ×ˢ sphere (0 : E) 1
  let f (p : ℝ × E) := c + p.1 • p.2
  have hA : IsConnected A := (isConnected_Ioo hr).prod (isConnected_sphere hRank 0 zero_le_one)
  have hf : Continuous f := continuous_const.add (continuous_fst.smul continuous_snd)
  have hImage : f '' A = ball c r \ {c} := by
    ext x
    constructor
    · rintro ⟨⟨t, v⟩, ⟨ht, hv⟩, rfl⟩
      have hn := mem_sphere_zero_iff_norm.mp hv
      have hd : dist (f (t, v)) c = t := by
        rw [dist_eq_norm]
        change ‖c + t • v - c‖ = t
        rw [add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_pos ht.1, hn, mul_one]
      refine ⟨mem_ball.mpr (hd.trans_lt ht.2), ?_⟩
      intro he
      exact ht.1.ne' (hd.symm.trans (by rw [mem_singleton_iff.mp he, dist_self]))
    · rintro ⟨hx, hxneq⟩
      let t := ‖x - c‖
      have ht : 0 < t := norm_pos_iff.mpr (sub_ne_zero.mpr (fun h => hxneq (mem_singleton_iff.mpr h)))
      let v := t⁻¹ • (x - c)
      have hv : v ∈ sphere (0 : E) 1 := by
        apply mem_sphere_zero_iff_norm.mpr
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr ht.le)]
        exact inv_mul_cancel₀ ht.ne'
      refine ⟨(t, v), ⟨⟨ht, by simpa only [mem_ball, dist_eq_norm] using hx⟩, hv⟩, ?_⟩
      change c + t • (t⁻¹ • (x - c)) = x
      rw [smul_smul, mul_inv_cancel₀ ht.ne', one_smul, add_comm, sub_add_cancel]
  rw [← hImage]
  exact hA.image f hf.continuousOn

end Ball

section Manifold

open CalderonN (X)

variable {n : ℕ} [NeZero n] {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace n) M]

local notation "J" => 𝓡∂ n

private theorem exists_interiorBall_in_nhds
    {p : M} (hp : p ∈ (𝓡∂ n).interior M) {U : Set M} (hU : U ∈ 𝓝 p) :
    let e := extChartAt J p
    ∃ r > 0, ball (e p) r ⊆ e.target ∧
      e.symm '' ball (e p) r ⊆ U ∧ e.symm '' ball (e p) r ∈ 𝓝 p := by
  let e := extChartAt J p
  have hs : p ∈ e.source := mem_extChartAt_source p
  have hi : e p ∈ interior e.target := (ModelWithCorners.isInteriorPoint_iff (I := J)).1 hp
  have hMap : e.symm ⁻¹' U ∈ 𝓝 (e p) :=
    (continuousAt_extChartAt_symm (I := J) p).preimage_mem_nhds (by rwa [e.left_inv hs])
  obtain ⟨r, hr, hB⟩ := Metric.mem_nhds_iff.mp
    (inter_mem (isOpen_interior.mem_nhds hi) hMap)
  have hBt : ball (e p) r ⊆ e.target := fun _ hx => interior_subset (hB hx).1
  refine ⟨r, hr, hBt, image_subset_iff.2 (fun _ hx => (hB hx).2), ?_⟩
  have hV : e.source ∩ e ⁻¹' ball (e p) r ∈ 𝓝 p :=
    inter_mem ((isOpen_extChartAt_source p).mem_nhds hs)
      ((continuousAt_extChartAt p).preimage_mem_nhds (ball_mem_nhds _ hr))
  exact mem_of_superset hV (fun x hx => ⟨e x, hx.2, e.left_inv hx.1⟩)

private theorem inverseChart_puncturedBall
    (p : M) (r : ℝ) (hp : p ∈ (extChartAt J p).source)
    (hB : ball (extChartAt J p p) r ⊆ (extChartAt J p).target) :
    let e := extChartAt J p
    e.symm '' (ball (e p) r \ {e p}) = (e.symm '' ball (e p) r) \ {p} := by
  let e := extChartAt J p
  ext z
  constructor
  · rintro ⟨x, ⟨hx, hxne⟩, rfl⟩
    refine ⟨mem_image_of_mem e.symm hx, ?_⟩
    intro hq
    have h := congrArg e (mem_singleton_iff.mp hq)
    rw [e.right_inv (hB hx)] at h
    exact hxne (mem_singleton_iff.mpr h)
  · rintro ⟨⟨x, hx, rfl⟩, hz⟩
    refine ⟨x, ⟨hx, ?_⟩, rfl⟩
    intro h
    exact hz (mem_singleton_iff.mpr ((congrArg e.symm (mem_singleton_iff.mp h)).trans (e.left_inv hp)))

/-- Removing an interior point from a connected open interior domain in
dimension at least two preserves connectedness. -/
theorem isConnected_interior_sdiff_singleton [T2Space M] (hRank : 1 < Module.rank ℝ (X n))
    {U : Set M} (hU : IsOpen U) (hConn : IsConnected U) (hInt : U ⊆ (𝓡∂ n).interior M)
    (p : M) : IsConnected (U \ {p}) := by
  let S := U \ {p}
  have hpChart : p ∈ (extChartAt J p).source := mem_extChartAt_source p
  have hSp : IsOpen S := hU.sdiff isClosed_singleton
  have hDense : U ⊆ closure S := by
    intro x hx
    by_cases hxne : x = p
    · subst x
      apply mem_closure_iff_nhds.2
      intro V hV
      obtain ⟨r, hr, ht, hSub, _⟩ :=
        exists_interiorBall_in_nhds (hInt hx) (inter_mem hV (hU.mem_nhds hx))
      let e := extChartAt J p
      obtain ⟨z, hz, hzNe⟩ := (isConnected_puncturedBall hRank (e p) hr).1
      have hY := hSub (mem_image_of_mem e.symm hz)
      have hYne : e.symm z ∉ ({p} : Set M) := by
        intro heq
        have h := congrArg e (mem_singleton_iff.mp heq)
        rw [e.right_inv (ht hz)] at h
        exact hzNe (mem_singleton_iff.mpr h)
      exact ⟨e.symm z, hY.1, hY.2, hYne⟩
    · exact subset_closure ⟨hx, fun h => hxne (mem_singleton_iff.mp h)⟩
  obtain ⟨x, hx⟩ := hConn.1
  refine ⟨closure_nonempty_iff.mp ⟨x, hDense hx⟩,
    isPreconnected_of_dense_local_intersections hConn.2 sdiff_subset hDense ?_⟩
  intro x hxU
  by_cases hx : x = p
  · subst x
    obtain ⟨r, hr, ht, hSub, hV⟩ := exists_interiorBall_in_nhds (hInt hxU) (hU.mem_nhds hxU)
    let e := extChartAt J p
    refine ⟨e.symm '' ball (e p) r, hV, ?_⟩
    have hEq : (e.symm '' ball (e p) r) ∩ S = e.symm '' (ball (e p) r \ {e p}) := by
      rw [inverseChart_puncturedBall p r hpChart ht]
      ext y
      exact ⟨fun h => ⟨h.1, h.2.2⟩, fun h => ⟨h.1, hSub h.1, h.2⟩⟩
    rw [hEq]
    exact (isConnected_puncturedBall hRank (e p) hr).2.image e.symm
      ((continuousOn_extChartAt_symm p).mono (fun _ h => ht h.1))
  · have hxS : x ∈ S := ⟨hxU, fun h => hx (mem_singleton_iff.mp h)⟩
    obtain ⟨r, hr, ht, hSub, hV⟩ := exists_interiorBall_in_nhds (hInt hxU) (hSp.mem_nhds hxS)
    let e := extChartAt J x
    refine ⟨e.symm '' ball (e x) r, hV, ?_⟩
    rw [inter_eq_left.mpr hSub]
    exact (Metric.isConnected_ball hr).2.image e.symm ((continuousOn_extChartAt_symm x).mono ht)

/-- Domains used for continuation remain connected after excising a
finite set of Green poles. -/
theorem isConnected_interior_sdiff_finite [T2Space M] (hn : 2 ≤ n)
    {U : Set M} (hU : IsOpen U) (hConn : IsConnected U) (hInt : U ⊆ (𝓡∂ n).interior M)
    {K : Set M} (hK : K.Finite) : IsConnected (U \ K) := by
  have hRank : 1 < Module.rank ℝ (X n) := by
    rw [← Module.finrank_eq_rank, finrank_euclideanSpace_fin]
    exact_mod_cast (show 1 < n from hn)
  induction K, hK using Set.Finite.induction_on with
  | empty => simpa only [sdiff_empty] using hConn
  | @insert p K _ hK ih =>
    have hEq : U \ insert p K = (U \ K) \ {p} := by
      ext x
      simp only [Set.mem_sdiff, mem_insert_iff, mem_singleton_iff, not_or]
      tauto
    rw [hEq]
    exact isConnected_interior_sdiff_singleton hRank (hU.sdiff hK.isClosed) ih
      (sdiff_subset.trans hInt) p

end Manifold

end CalderonPatch
