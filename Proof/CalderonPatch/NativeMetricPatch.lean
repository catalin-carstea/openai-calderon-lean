module

public import Proof.CalderonPatch.CoordinateMetricSection

import Mathlib.Analysis.LocallyConvex.Bounded
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.Tactic.Linarith

public section

noncomputable section
open Bundle Filter Metric Set Bornology
open scoped ContDiff Manifold Topology

namespace CalderonPatch

open CalderonN (X MetricField metricPair)

variable {n : ℕ} [NeZero n] {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace n) M] [IsManifold (𝓡∂ n) ∞ M]

local notation "J" => 𝓡∂ n
local notation "K" => 𝓘(ℝ, X n)
local notation "T" => TangentSpace J
local notation "B" => (X n →L[ℝ] X n →L[ℝ] ℝ)
local notation "JB" => (ModelWithCorners.prod J 𝓘(ℝ, B))

private theorem isVonNBounded_coordinateMetric_unit {γ : MetricField n} {z : X n}
    (hp : (γ z).PosDef) {A : X n →L[ℝ] X n} (hA : Function.Injective A) :
    IsVonNBounded ℝ {v : X n | metricPair γ z (A v) (A v) < 1} := by
  obtain ⟨c,C,hc,_,hBound⟩ := CalderonN.exists_uniform_metric_comparison
    (isCompact_singleton (x := z))
    (fun i j => continuousOn_singleton (fun y => γ y i j) z)
    (fun x hx => (mem_singleton_iff.mp hx).symm ▸ hp)
  have hSurj := LinearMap.injective_iff_surjective.mp hA
  let L := ContinuousLinearEquiv.ofBijective A (LinearMap.ker_eq_bot.mpr hA) (LinearMap.range_eq_top.mpr hSurj)
  let S := {v : X n | metricPair γ z v v < 1}
  have hS : IsVonNBounded ℝ S := by
    apply (NormedSpace.isVonNBounded_iff ℝ).mpr
    apply (isBounded_closedBall (x := (0 : X n)) (r := Real.sqrt (1/c))).subset
    intro v hv
    rw [mem_closedBall_zero_iff]
    apply Real.le_sqrt_of_sq_le
    refine (le_div_iff₀ hc).mpr ?_
    have h := (hBound z (mem_singleton z) v).1
    change c * ‖v‖^2 ≤ metricPair γ z v v at h
    linarith only [h, show metricPair γ z v v < 1 from hv]
  apply (hS.image (L.symm : X n →L[ℝ] X n)).subset
  intro v hv
  exact ⟨A v,hv,L.symm_apply_apply v⟩

/-- Replace a native metric by a smooth positive coordinate field in
a chart. Agreement away from the closed support makes the result
smooth on the original manifold type, including its boundary. -/
theorem exists_nativeMetric_of_coordinate_replacement (g : SmoothMetric n M)
    {U A : Set M} (hU : IsOpen U) (hA : IsClosed A) (hAU : A ⊆ U)
    {V : Set (X n)} {γ : MetricField n} (hγ : CalderonN.SmoothMetric V γ)
    {q : M → X n} (hq : ContMDiffOn J K ∞ q U) (hqV : MapsTo q U V)
    (hInjective : ∀ x ∈ U, Function.Injective (mfderiv J K q x))
    (hAgree : ∀ x ∈ U \ A, nativeCoordinateBilinear γ q x = g.inner x) :
    ∃ g' : SmoothMetric n M,
      (∀ x ∈ U, g'.inner x = nativeCoordinateBilinear γ q x) ∧
      (∀ x ∉ A, g'.inner x = g.inner x) := by
  classical
  let b (x : M) := if x ∈ U then nativeCoordinateBilinear γ q x else g.inner x
  have hBU (x : M) (hx : x ∈ U) : b x = nativeCoordinateBilinear γ q x := if_pos hx
  have hBA (x : M) (hx : x ∉ A) : b x = g.inner x := by
    by_cases hu : x ∈ U
    · exact (hBU x hu).trans (hAgree x ⟨hu,hx⟩)
    · exact if_neg hu
  have hB : ContMDiff J JB ∞ (fun x => TotalSpace.mk' B x (b x)) := by
    intro x
    by_cases hx : x ∈ U
    · have hb := (contMDiffOn_nativeCoordinateBilinear hU hγ hq hqV).contMDiffAt (hU.mem_nhds hx)
      apply hb.congr_of_eventuallyEq
      filter_upwards [hU.mem_nhds hx] with y hy
      rw [hBU y hy]
    · have hn : x ∈ Aᶜ := fun hxA => hx (hAU hxA)
      apply (g.contMDiff x).congr_of_eventuallyEq
      filter_upwards [hA.isOpen_compl.mem_nhds hn] with y hy
      rw [hBA y hy]
  let g' : SmoothMetric n M :=
    { inner := b
      symm := fun x v w => by
        by_cases hx : x ∈ U
        · rw [hBU x hx, nativeCoordinateBilinear_apply, nativeCoordinateBilinear_apply]
          exact CalderonN.metricPair_comm (hγ.2 _ (hqV hx)) _ _
        · rw [hBA x (fun h => hx (hAU h))]
          exact g.symm x v w
      pos := fun x v hv => by
        by_cases hx : x ∈ U
        · rw [hBU x hx, nativeCoordinateBilinear_apply]
          exact CalderonN.metricPair_pos_of_posDef (hγ.2 _ (hqV hx))
            (fun h => hv ((hInjective x hx) (h.trans ((mfderiv J K q x).map_zero).symm)))
        · rw [hBA x (fun h => hx (hAU h))]
          exact g.pos x v hv
      isVonNBounded := fun x => by
        by_cases hx : x ∈ U
        · let D : X n →L[ℝ] X n := mfderiv J K q x
          have hD : Function.Injective D := hInjective x hx
          have h := isVonNBounded_coordinateMetric_unit (hγ.2 _ (hqV hx)) hD
          apply h.subset
          intro v hv
          change b x v v < 1 at hv
          rw [hBU x hx] at hv
          exact lt_of_eq_of_lt (nativeCoordinateBilinear_apply γ q x (v : T x) (v : T x)).symm hv
        · rw [hBA x (fun h => hx (hAU h))]
          exact g.isVonNBounded x
      contMDiff := hB }
  exact ⟨g',hBU,hBA⟩

end CalderonPatch
