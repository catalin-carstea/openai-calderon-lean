module

public import Proof.CalderonPatch.Energy
import Mathlib.Tactic

@[expose] public section

noncomputable section
open Filter Set MeasureTheory
open scoped ContDiff Manifold Topology

namespace CalderonPaper

open CalderonN (X axis)
open CalderonPatch

section Boundary

variable {n : ℕ} [NeZero n] {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace n) M] [IsManifold (𝓡∂ n) ∞ M]

local notation "J" => 𝓡∂ n
set_option quotPrecheck false in
local notation "B" => ((𝓡∂ n).boundary M)

theorem boundary_compl_singleton_dense (hn : 2 ≤ n) (p : ↥B) :
    Dense ({p}ᶜ : Set ↥B) := by
  intro q
  by_cases hq : q = p
  · subst q
    rw [mem_closure_iff]
    intro O hO hpO
    obtain ⟨W, hW, rfl⟩ := isOpen_induced_iff.mp hO
    let e := extChartAt J (p : M)
    let x := e p
    have hs : (p : M) ∈ e.source := mem_extChartAt_source _
    have hx : x ∈ e.target := e.map_source hs
    have hxp : e.symm x = (p : M) := e.left_inv hs
    have hrange : range (J : EuclideanHalfSpace n → X n) = {y | 0 ≤ y 0} :=
      range_euclideanHalfSpace n
    have hx0 : x 0 = 0 := by
      have h := ((J).isBoundaryPoint_iff (x := (p : M))).mp p.property
      change x ∈ frontier (range (J : EuclideanHalfSpace n → X n)) at h
      rw [hrange, frontier_halfSpace] at h
      exact h.symm
    let i : Fin n := ⟨1, by omega⟩
    have hi : i ≠ (0 : Fin n) := by
      intro h
      have := congrArg Fin.val h
      simp [i] at this
    let line (t : ℝ) : X n := x + t • axis i
    have hline0 (t : ℝ) : line t 0 = 0 := by
      simp [line, hx0, axis, Ne.symm hi]
    have hline : Tendsto line (𝓝[≠] (0 : ℝ)) (𝓝 x) := by
      have hc : Continuous line := continuous_const.add (continuous_id.smul continuous_const)
      simpa [line] using hc.continuousAt.tendsto.mono_left
        (nhdsWithin_le_nhds : 𝓝[≠] (0 : ℝ) ≤ 𝓝 0)
    have hline' : Tendsto line (𝓝[≠] (0 : ℝ)) (𝓝[e.target] x) := by
      rw [nhdsWithin_extChartAt_target_eq_of_mem hx]
      apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within line hline
      exact Filter.Eventually.of_forall fun t => by
        rw [hrange]
        change 0 ≤ line t 0
        simp [hline0]
    have heW : ∀ᶠ z in 𝓝[e.target] x, e.symm z ∈ W := by
      have hc : ContinuousWithinAt e.symm e.target x :=
        (continuousOn_extChartAt_symm (I := J) (p : M)) x hx
      apply hc
      apply hW.mem_nhds
      rw [hxp]
      exact hpO
    have hnear : ∀ᶠ t in 𝓝[≠] (0 : ℝ), line t ∈ e.target ∧ e.symm (line t) ∈ W ∧ t ≠ 0 := by
      filter_upwards [hline' self_mem_nhdsWithin, hline' heW,
        (self_mem_nhdsWithin : {t : ℝ | t ≠ 0} ∈ 𝓝[≠] (0 : ℝ))] with t ht hw hne
      exact ⟨ht, hw, hne⟩
    obtain ⟨t, ht, htw, ht0⟩ := hnear.exists
    let y := e.symm (line t)
    have hyS : y ∈ e.source := e.map_target ht
    have hy : e y = line t := e.right_inv ht
    have hyB : y ∈ B := by
      have hyChart : y ∈ (chartAt (EuclideanHalfSpace n) (p : M)).source := by
        simpa only [e, extChartAt_source] using hyS
      apply ((J).isBoundaryPoint_iff_of_mem_atlas (n := ∞) (by simp)
        (chart_mem_atlas (EuclideanHalfSpace n) (p : M)) hyChart).mpr
      change e y ∈ frontier e.target
      rw [hy]
      change line t ∈ closure e.target \ interior e.target
      constructor
      · exact subset_closure ht
      · intro hint
        have hmodel := (extChartAt_target_eventuallyEqSet_of_mem ht).mem_interior hint
        rw [hrange, interior_halfSpace] at hmodel
        simp [hline0] at hmodel
    refine ⟨⟨y, hyB⟩, htw, ?_⟩
    intro hp
    change (⟨y, hyB⟩ : ↥B) = p at hp
    have hxline : line t = x := hy.symm.trans (congrArg (fun z : ↥B => e z) hp)
    have hiEq := congrArg (fun z : X n => z i) hxline
    have hzero : x i + t = x i := by
      simpa [line, axis] using hiEq
    exact ht0 (by linarith)
  · exact subset_closure hq

end Boundary

end CalderonPaper
