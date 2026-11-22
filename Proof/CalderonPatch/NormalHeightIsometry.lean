module

public import Proof.CalderonPatch.BoundaryNormalLaplacian
public import Proof.CalderonPatch.BoundaryNormalSide
public import Proof.CalderonN.MetricConnection

import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

public section

noncomputable section
open Filter Matrix Metric Set
open scoped ContDiff Topology

namespace CalderonPatch

open CalderonN (I X MetricField axis metricPair metricBilinear metricBilinear_apply)

variable {n : ℕ} {i : I n} {U : Set (X n)} {g : MetricField n}

theorem normalMetric_pair_axis (h : HasNormalMetricBlock i g U) {x : X n} (hx : x ∈ U) (w : X n) :
    metricPair g x (axis i) w = w i := by
  rw [CalderonN.metricPair_axis_left]
  simp only [h x hx, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ite_true]

theorem normalMetric_sq_decompose (h : HasNormalMetricBlock i g U) {x : X n}
    (hx : x ∈ U) (hp : (g x).PosDef) (w : X n) :
    metricPair g x w w = w i ^ 2 + metricPair g x (boundaryFoot i w) (boundaryFoot i w) := by
  let b := boundaryFoot i w
  have hAxis : axis i i = 1 := by simp [axis]
  have hDiag := normalMetric_pair_axis h hx (axis i)
  rw [hAxis] at hDiag
  have hOrth := normalMetric_pair_axis h hx b
  change metricPair g x (axis i) b = boundaryFoot i w i at hOrth
  rw [boundaryFoot_coord] at hOrth
  have hO' := (CalderonN.metricPair_comm hp b (axis i)).trans hOrth
  simp only [← metricBilinear_apply] at hDiag hOrth hO' ⊢
  conv_lhs => rw [← boundaryFoot_add_axis i w]
  change ((metricBilinear g x) (b + w i • axis i)) (b + w i • axis i) =
    w i ^ 2 + metricBilinear g x b b
  simp only [map_add, _root_.add_apply, map_smul, _root_.smul_apply, smul_eq_mul, hOrth, hO', hDiag]
  ring

theorem coordinate_abs_le_of_normal_unit (h : HasNormalMetricBlock i g U)
    {x : X n} (hx : x ∈ U) (hp : (g x).PosDef) {w : X n} (hw : metricPair g x w w = 1) :
    |w i| ≤ 1 := by
  have ha := normalMetric_sq_decompose h hx hp w
  have hPos := CalderonN.metricPair_nonneg_of_posDef hp (boundaryFoot i w)
  rw [hw] at ha
  apply abs_le_of_sq_le_sq _ zero_le_one
  rw [one_pow]
  linarith

theorem eq_axis_of_normal_unit_and_height_one (h : HasNormalMetricBlock i g U)
    {x : X n} (hx : x ∈ U) (hp : (g x).PosDef) {w : X n}
    (hw : metricPair g x w w = 1) (hwi : w i = 1) : w = axis i := by
  have ha := normalMetric_sq_decompose h hx hp w
  rw [hw, hwi, one_pow] at ha
  have hZ : boundaryFoot i w = 0 := by
    by_contra hz
    have hP := CalderonN.metricPair_pos_of_posDef hp hz
    linarith
  rw [← boundaryFoot_add_axis i w, hZ, hwi, one_smul, zero_add]

variable {j : I n} {V : Set (X n)} {g' : MetricField n}

/-- The image of a unit-speed normal segment under an interior metric
isometry cannot rise farther from the target coordinate seam. The
argument uses continuity to reach the initial boundary point. -/
theorem normalHeight_le_of_isometry_on_segment
    {z : X n} {t : ℝ} (ht : 0 < t)
    (hN : HasNormalMetricBlock i g U) (hN' : HasNormalMetricBlock j g' V)
    (hV : ∀ x ∈ V, (g' x).PosDef)
    {f : X n → X n} (hStart : f z j = 0)
    (hC : ContinuousOn (fun s : ℝ => f (z + s • axis i) j) (Icc 0 t))
    (hInterior : ∀ s ∈ Ioo 0 t, z + s • axis i ∈ U)
    (hMaps : MapsTo f U V)
    (hf : ∀ x ∈ U, DifferentiableAt ℝ f x)
    (hIsom : ∀ x ∈ U, ∀ v w, metricPair g x v w =
      metricPair g' (f x) (fderiv ℝ f x v) (fderiv ℝ f x w)) :
    f (z + t • axis i) j ≤ t := by
  let F : ℝ → ℝ := fun s => f (z + s • axis i) j
  have hAxis : axis i i = 1 := by simp [axis]
  have hDer (s : ℝ) (hs : s ∈ Ioo 0 t) :
      HasDerivAt F (fderiv ℝ f (z + s • axis i) (axis i) j) s := by
    have hA : HasDerivAt (fun s : ℝ => z + s • axis i) (axis i) s := by
      simpa only [id_eq, one_smul, zero_add] using
        HasDerivAt.fun_add (hasDerivAt_const s z) ((hasDerivAt_id s).smul_const (axis i))
    have hf' : HasDerivAt (f ∘ fun s : ℝ => z + s • axis i)
        (fderiv ℝ f (z + s • axis i) (axis i)) s :=
      (hf _ (hInterior s hs)).hasFDerivAt.comp_hasDerivAt s hA
    let p : X n →L[ℝ] ℝ := EuclideanSpace.proj j
    change HasDerivAt (p ∘ (f ∘ fun s : ℝ => z + s • axis i)) _ s
    exact p.hasFDerivAt.comp_hasDerivAt s hf'
  obtain ⟨s,hs,hM⟩ := exists_hasDerivAt_eq_slope F
    (fun s => fderiv ℝ f (z + s • axis i) (axis i) j) ht hC hDer
  have hAt := hInterior s hs
  have hUnit := (hIsom _ hAt (axis i) (axis i)).symm.trans
    ((normalMetric_pair_axis hN hAt (axis i)).trans hAxis)
  have hVAt := hMaps hAt
  have hsBound := coordinate_abs_le_of_normal_unit hN' hVAt (hV _ hVAt) hUnit
  have hF₀ : F 0 = 0 := by simpa only [F, zero_smul, add_zero] using hStart
  rw [hM, hF₀, sub_zero, sub_zero] at hsBound
  have hh := (abs_le.mp hsBound).2
  change F t ≤ t
  simpa only [one_mul] using (div_le_iff₀ ht).mp hh

/-- If a smooth interior isometry preserves the normal height, its
derivative sends the unit normal to the unit normal. -/
theorem maps_normal_axis_of_height_eq (hU : IsOpen U)
    (hN : HasNormalMetricBlock i g U) (hN' : HasNormalMetricBlock j g' V)
    (hV : ∀ x ∈ V, (g' x).PosDef)
    {f : X n → X n} (hMaps : MapsTo f U V) {x : X n} (hx : x ∈ U)
    (hf : DifferentiableAt ℝ f x)
    (hHeight : ∀ x ∈ U, f x j = x i)
    (hIsom : ∀ v w, metricPair g x v w =
      metricPair g' (f x) (fderiv ℝ f x v) (fderiv ℝ f x w)) :
    fderiv ℝ f x (axis i) = axis j := by
  have heq : (fun y => f y j) =ᶠ[𝓝 x] fun y => y i :=
    Filter.mem_of_superset (hU.mem_nhds hx) (fun _ hy => hHeight _ hy)
  let pj : X n →L[ℝ] ℝ := EuclideanSpace.proj j
  let pi : X n →L[ℝ] ℝ := EuclideanSpace.proj i
  have hh : pj.comp (fderiv ℝ f x) = pi :=
    ((pj.hasFDerivAt.comp x hf.hasFDerivAt).congr_of_eventuallyEq heq.symm).unique pi.hasFDerivAt
  have hAxis : axis i i = 1 := by simp [axis]
  have hS := DFunLike.congr_fun hh (axis i)
  change fderiv ℝ f x (axis i) j = axis i i at hS
  have hUnit := (hIsom (axis i) (axis i)).symm.trans ((normalMetric_pair_axis hN hx _).trans hAxis)
  exact eq_axis_of_normal_unit_and_height_one hN' (hMaps hx) (hV _ (hMaps hx)) hUnit (hS.trans hAxis)

end CalderonPatch
