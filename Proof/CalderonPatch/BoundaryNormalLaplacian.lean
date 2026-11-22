module

public import Proof.CalderonPatch.PointLaplaceOrder
public import Proof.CalderonN.MetricVolumeDifferential

import Proof.CalderonN.MetricCompatibility
import Mathlib.Tactic.Ring

@[expose] public section

noncomputable section
open Filter Matrix Set
open scoped Topology

namespace CalderonPatch

open CalderonN (I X Mat MetricField axis coordDeriv christoffel laplace matrixFieldDerivative)

variable {n : ℕ} {U : Set (X n)} {g : MetricField n} {i : I n}

/-- The (i)-th coordinate is the unit normal and orthogonal to the
coordinate slices. -/
def HasNormalMetricBlock (i : I n) (g : MetricField n) (U : Set (X n)) : Prop :=
  ∀ x ∈ U, ∀ j, g x i j = if i = j then 1 else 0

theorem inverse_normalMetricBlock_row (hN : HasNormalMetricBlock i g U)
    {x : X n} (hx : x ∈ U) (hp : (g x).PosDef) (j : I n) :
    (g x)⁻¹ i j = if i = j then 1 else 0 := by
  have h := congrArg (fun A : Mat n => A i j)
    (Matrix.mul_nonsing_inv (g x) (isUnit_iff_ne_zero.mpr hp.det_pos.ne'))
  simpa only [Matrix.mul_apply, Matrix.one_apply, hN x hx, ite_mul, one_mul, zero_mul,
    Finset.sum_ite_eq, Finset.mem_univ, ite_true] using h

theorem metricBlock_normal_connection (hU : IsOpen U) (hg : CalderonN.SmoothMetric U g)
    (hN : HasNormalMetricBlock i g U) {x : X n} (hx : x ∈ U) (a b : I n) :
    christoffel g x i a b = -coordDeriv i (fun y => g y a b) x / 2 := by
  have hRow (j k : I n) : coordDeriv k (fun y => g y i j) x = 0 := by
    have he : (fun y => g y i j) =ᶠ[𝓝 x] fun _ => if i = j then 1 else 0 :=
      Filter.mem_of_superset (hU.mem_nhds hx) (fun y hy => hN y hy j)
    simp only [coordDeriv, he.fderiv_eq, fderiv_const_apply, _root_.zero_apply]
  have hCol (j k : I n) : coordDeriv k (fun y => g y j i) x = 0 := by
    have he : (fun y => g y j i) =ᶠ[𝓝 x] fun y => g y i j :=
      Filter.mem_of_superset (hU.mem_nhds hx) (fun y hy => by
        exact congrFun (congrFun (hg.2 y hy).isHermitian.isSymm i) j)
    have h := hRow j k
    simpa only [coordDeriv, he.fderiv_eq] using h
  simp only [christoffel, inverse_normalMetricBlock_row hN hx (hg.2 _ hx), ite_mul, one_mul, zero_mul,
    Finset.sum_ite_eq, Finset.mem_univ, ite_true, hRow, hCol, zero_add, zero_sub]

theorem laplace_normal_firstCoeff (hU : IsOpen U) (hg : CalderonN.SmoothMetric U g)
    (hN : HasNormalMetricBlock i g U) {x : X n} (hx : x ∈ U) :
    laplaceFirstCoeff g x i = ((g x)⁻¹ * matrixFieldDerivative g x (axis i)).trace / 2 := by
  simp only [laplaceFirstCoeff, metricBlock_normal_connection hU hg hN hx,
    mul_neg, Finset.sum_neg_distrib, neg_div, neg_neg,
    Matrix.trace, Matrix.diag, Matrix.mul_apply, CalderonN.matrixFieldDerivative_apply_entry]
  have hSym (a b : I n) : fderiv ℝ (fun y => g y b a) x (axis i) =
      fderiv ℝ (fun y => g y a b) x (axis i) := by
    have he : (fun y => g y b a) =ᶠ[𝓝 x] (fun y => g y a b) :=
      Filter.mem_of_superset (hU.mem_nhds hx) (fun y hy => by
        exact congrFun (congrFun (hg.2 y hy).isHermitian.isSymm a) b)
    rw [he.fderiv_eq]
  simp only [hSym, coordDeriv, ← mul_div_assoc, ← Finset.sum_div]

private theorem inverse_normal_col (hg : CalderonN.SmoothMetric U g)
    (hN : HasNormalMetricBlock i g U) {x : X n} (hx : x ∈ U) (j : I n) :
    (g x)⁻¹ j i = if i = j then 1 else 0 := by
  rw [← inverse_normalMetricBlock_row hN hx (hg.2 x hx) j]
  exact congrFun (congrFun (hg.2 x hx).inv.isHermitian.isSymm i) j

/-- The terms containing only derivatives in the coordinate slices. -/
def tangentialLaplace (i : I n) (g : MetricField n) (u : X n → ℝ) (x : X n) : ℝ :=
  (∑ a ∈ Finset.univ.erase i, ∑ b ∈ Finset.univ.erase i, (g x)⁻¹ a b * coordDeriv a (coordDeriv b u) x) +
    ∑ a ∈ Finset.univ.erase i, laplaceFirstCoeff g x a * coordDeriv a u x

/-- The native coordinate Laplacian in the signed normal chart is
the normal second derivative, the determinant drift, and a slice operator. -/
theorem laplace_eq_normal_split (hU : IsOpen U) (hg : CalderonN.SmoothMetric U g)
    (hN : HasNormalMetricBlock i g U) {x : X n} (hx : x ∈ U) (u : X n → ℝ) :
    laplace g u x = coordDeriv i (coordDeriv i u) x +
      (((g x)⁻¹ * matrixFieldDerivative g x (axis i)).trace / 2) * coordDeriv i u x +
      tangentialLaplace i g u x := by
  let A (a b : I n) := (g x)⁻¹ a b * coordDeriv a (coordDeriv b u) x
  let B (a : I n) := laplaceFirstCoeff g x a * coordDeriv a u x
  rw [← coordinateElliptic_eq_laplace]
  simp only [coordinateElliptic, Pi.add_apply, Finset.sum_apply, Pi.mul_apply,
    CalderonN.chartDerivativeWord, List.foldr_cons, List.foldr_nil]
  change (∑ a : I n, ∑ b : I n, A a b) + (∑ a : I n, B a) = _
  rw [← Finset.sum_erase_add Finset.univ (fun a => ∑ b : I n, A a b) (Finset.mem_univ i),
    ← Finset.sum_erase_add Finset.univ B (Finset.mem_univ i)]
  have hArow : (∑ b : I n, A i b) = coordDeriv i (coordDeriv i u) x := by
    simp only [A, inverse_normalMetricBlock_row hN hx (hg.2 _ hx), ite_mul, one_mul,
      zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  have hAcol (a : I n) (ha : a ∈ Finset.univ.erase i) :
      (∑ b : I n, A a b) = ∑ b ∈ Finset.univ.erase i, A a b := by
    rw [← Finset.sum_erase_add Finset.univ (A a) (Finset.mem_univ i)]
    simp [A, inverse_normal_col hg hN hx, (Finset.ne_of_mem_erase ha).symm]
  have hB : B i = (((g x)⁻¹ * matrixFieldDerivative g x (axis i)).trace / 2) * coordDeriv i u x := by
    simp only [B, laplace_normal_firstCoeff hU hg hN hx]
  have hs := Finset.sum_congr rfl (fun a ha => hAcol a ha)
  rw [hs, hArow, hB]
  unfold tangentialLaplace A B
  ring

end CalderonPatch
