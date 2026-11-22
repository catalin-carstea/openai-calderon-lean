module

public import Proof.CalderonN.Chart
public import Proof.CalderonN.InverseMetricBounds

import Proof.CalderonN.MetricPair
import Proof.CalderonN.SphereFrame
import Proof.CalderonN.MetricCalculus
import Mathlib.Tactic.FieldSimp
import Mathlib.Analysis.Calculus.ContDiff.WithLp

@[expose] public section

noncomputable section
open Matrix Set
open scoped ContDiff

namespace CalderonPatch

open CalderonN (I X Mat MetricField metricPair inverseMetricColumn)

variable {n : ℕ}

/-- The metric unit normal pointing toward increasing coordinate `i`.
It is the normalized metric dual of the coordinate covector. -/
def positiveCoordinateNormal (g : MetricField n) (i : I n) (x : X n) : X n :=
  (Real.sqrt ((g x)⁻¹ i i))⁻¹ • inverseMetricColumn g x i

theorem metricPair_inverseMetricColumn_left (g : MetricField n) {x : X n}
    (hg : (g x).PosDef) (i : I n) (u : X n) :
    metricPair g x (inverseMetricColumn g x i) u = u i := by
  have hSym : ((g x)⁻¹).transpose = (g x)⁻¹ := hg.inv.isHermitian.isSymm.eq
  have hInv := Matrix.nonsing_inv_mul (g x) (isUnit_iff_ne_zero.mpr hg.det_pos.ne')
  have hRow (j : I n) : (∑ k, (g x)⁻¹ k i * g x k j) = if i = j then 1 else 0 := by
    have hS (k : I n) : (g x)⁻¹ k i = (g x)⁻¹ i k := congrArg (fun A : Mat n => A i k) hSym
    simpa only [hS, Matrix.mul_apply, Matrix.one_apply] using congrArg (fun A : Mat n => A i j) hInv
  change (∑ k, ∑ j, g x k j * (g x)⁻¹ k i * u j) = u i
  rw [Finset.sum_comm]
  simp only [← Finset.sum_mul, mul_comm (g x _ _) ((g x)⁻¹ _ _), hRow, ite_mul, one_mul, zero_mul,
    Finset.sum_ite_eq, Finset.mem_univ, ite_true]

theorem positiveCoordinateNormal_coordinate (g : MetricField n) {x : X n}
    (hg : (g x).PosDef) (i : I n) : positiveCoordinateNormal g i x i = Real.sqrt ((g x)⁻¹ i i) := by
  change (Real.sqrt ((g x)⁻¹ i i))⁻¹ * (g x)⁻¹ i i = _
  have h : 0 < (g x)⁻¹ i i := hg.inv.diag_pos
  calc
    _ = (Real.sqrt ((g x)⁻¹ i i))⁻¹ * (Real.sqrt ((g x)⁻¹ i i)) ^ 2 :=
      congrArg ((Real.sqrt ((g x)⁻¹ i i))⁻¹ * ·) (Real.sq_sqrt h.le).symm
    _ = _ := by rw [pow_two, ← mul_assoc, inv_mul_cancel₀ (Real.sqrt_pos.mpr h).ne', one_mul]

theorem positiveCoordinateNormal_transverse (g : MetricField n) {x : X n}
    (hg : (g x).PosDef) (i : I n) : 0 < positiveCoordinateNormal g i x i := by
  rw [positiveCoordinateNormal_coordinate _ hg]
  exact Real.sqrt_pos.mpr hg.inv.diag_pos

theorem metricPair_positiveCoordinateNormal (g : MetricField n) {x : X n}
    (hg : (g x).PosDef) (i : I n) (u : X n) :
    metricPair g x (positiveCoordinateNormal g i x) u = (Real.sqrt ((g x)⁻¹ i i))⁻¹ * u i := by
  rw [positiveCoordinateNormal, CalderonN.metricPair_smul_left, metricPair_inverseMetricColumn_left g hg]

theorem positiveCoordinateNormal_unit (g : MetricField n) {x : X n}
    (hg : (g x).PosDef) (i : I n) :
    metricPair g x (positiveCoordinateNormal g i x) (positiveCoordinateNormal g i x) = 1 := by
  rw [metricPair_positiveCoordinateNormal _ hg, positiveCoordinateNormal_coordinate _ hg,
    inv_mul_cancel₀ (Real.sqrt_pos.mpr hg.inv.diag_pos).ne']

theorem contDiffOn_positiveCoordinateNormal {U : Set (X n)} {g : MetricField n}
    (hg : CalderonN.SmoothMetric U g) (i : I n) : ContDiffOn ℝ ∞ (positiveCoordinateNormal g i) U := by
  have hPos (x : X n) (hx : x ∈ U) : 0 < (g x)⁻¹ i i := (hg.2 x hx).inv.diag_pos
  have hRoot := (CalderonN.contDiffOn_metric_inv_entry hg i i).sqrt (fun x hx => (hPos x hx).ne')
  have hCol : ContDiffOn ℝ ∞ (fun x => inverseMetricColumn g x i) U := by
    apply (contDiffOn_piLp 2).mpr
    exact fun j => CalderonN.contDiffOn_metric_inv_entry hg j i
  exact (hRoot.inv fun x hx => (Real.sqrt_pos.mpr (hPos x hx)).ne').smul hCol

end CalderonPatch
