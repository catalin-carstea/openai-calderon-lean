module

public import Proof.CalderonN.MetricPair

import Proof.CalderonN.ChartBilinear
import Proof.CalderonN.MetricConnection
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Tactic

@[expose] public section

noncomputable section
open Set Matrix Filter
open scoped ContDiff Topology

namespace CalderonN

variable {dim : ℕ} [NeZero dim]

private theorem metric_entry_symm {U : Set (X dim)} {g : (MetricField dim)}
    (hg : SmoothMetric U g) {x : (X dim)} (hx : x ∈ U) (i j : (I dim)) : g x i j = g x j i :=
  (congrFun (congrFun (hg.2 x hx).isHermitian.isSymm.eq i) j).symm

private theorem coordDeriv_metric_entry_symm {U : Set (X dim)} (hU : IsOpen U) {g : (MetricField dim)}
    (hg : SmoothMetric U g) {x : (X dim)} (hx : x ∈ U) (k i j : (I dim)) :
    coordDeriv k (fun y => g y i j) x = coordDeriv k (fun y => g y j i) x := by
  have h : (fun y => g y i j) =ᶠ[𝓝 x] fun y => g y j i :=
    eventually_of_mem (hU.mem_nhds hx) (fun _ hz => metric_entry_symm hg hz i j)
  simp only [coordDeriv,h.fderiv_eq]

theorem christoffel_comm {U : Set (X dim)} (hU : IsOpen U) {g : (MetricField dim)}
    (hg : SmoothMetric U g) {x : (X dim)} (hx : x ∈ U) (k i j : (I dim)) :
    christoffel g x k i j = christoffel g x k j i := by
  unfold christoffel
  congr 1
  apply Finset.sum_congr rfl
  intro l _
  rw [coordDeriv_metric_entry_symm hU hg hx j i l,
    coordDeriv_metric_entry_symm hU hg hx i j l,
    coordDeriv_metric_entry_symm hU hg hx l i j]
  ring

theorem connection_comm {U : Set (X dim)} (hU : IsOpen U) {g : (MetricField dim)}
    (hg : SmoothMetric U g) {x : (X dim)} (hx : x ∈ U) (u v : (X dim)) :
    connection g x u v = connection g x v u := by
  ext k
  change (∑ i, ∑ j, christoffel g x k i j * u i * v j) =
    ∑ i, ∑ j, christoffel g x k i j * v i * u j
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [christoffel_comm hU hg hx k j i]
  ring

private theorem lowered_christoffel {g : (MetricField dim)} {x : (X dim)} (hg : (g x).PosDef) (l i j : (I dim)) :
    2 * ∑ k, g x l k * christoffel g x k i j =
      coordDeriv i (fun y => g y l j) x + coordDeriv j (fun y => g y i l) x -
        coordDeriv l (fun y => g y i j) x := by
  let D (m : (I dim)) := coordDeriv i (fun y => g y m j) x + coordDeriv j (fun y => g y i m) x -
    coordDeriv m (fun y => g y i j) x
  have hI (m : (I dim)) : ∑ k, g x l k * (g x)⁻¹ k m = if l = m then 1 else 0 := by
    have h := Matrix.mul_nonsing_inv (g x) (isUnit_iff_ne_zero.mpr hg.det_pos.ne')
    simpa only [Matrix.mul_apply,Matrix.one_apply] using congrFun (congrFun h l) m
  calc
    _ = ∑ k, ∑ m, (g x l k * (g x)⁻¹ k m) * D m := by
      unfold christoffel
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k _
      rw [show 2 * (g x l k * ((∑ l, (g x)⁻¹ k l * D l) / 2)) =
        g x l k * (∑ l, (g x)⁻¹ k l * D l) by ring, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro m _
      ring
    _ = ∑ m, (∑ k, g x l k * (g x)⁻¹ k m) * D m := by
      rw [Finset.sum_comm]
      simp only [Finset.sum_mul]
    _ = D l := by
      simp [hI,ite_mul]

private theorem metric_compatibility_entries {U : Set (X dim)} (hU : IsOpen U) {g : (MetricField dim)}
    (hg : SmoothMetric U g) {x : (X dim)} (hx : x ∈ U) (i j l : (I dim)) :
    coordDeriv i (fun y => g y j l) x =
      (∑ k, g x k l * christoffel g x k i j) + ∑ k, g x j k * christoffel g x k i l := by
  have h₁ := lowered_christoffel (hg.2 x hx) l i j
  have h₂ := lowered_christoffel (hg.2 x hx) j i l
  simp only [metric_entry_symm hg hx l,coordDeriv_metric_entry_symm hU hg hx i l j] at h₁
  linarith only [h₁,h₂]

/-- The directional derivative of the metric in its base variable equals
the sum of the two connection contractions. -/
theorem directional_metric_compatibility {U : Set (X dim)} (hU : IsOpen U) {g : (MetricField dim)}
    (hg : SmoothMetric U g) {x : (X dim)} (hx : x ∈ U) (a u v : (X dim)) :
    (∑ j, ∑ l, fderiv ℝ (fun y => g y j l) x a * u j * v l) =
      metricPair g x (connection g x a u) v + metricPair g x u (connection g x a v) := by
  have hb (i j l : I dim) :
      metricDifferential g x (axis i) (axis j) (axis l) =
        metricBilinear g x (connectionBilinear g x (axis i) (axis j)) (axis l) +
        metricBilinear g x (axis j) (connectionBilinear g x (axis i) (axis l)) := by
    rw [metricBilinear_apply, metricBilinear_apply, connectionBilinear_apply, connectionBilinear_apply,
      metricPair_axis_left, metricPair_axis_right]
    simp_rw [connection_axis_components]
    simp only [metricDifferential_apply, axis, EuclideanSpace.single_apply, mul_ite, ite_mul,
      mul_one, mul_zero, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    exact metric_compatibility_entries hU hg hx i j l
  rw [← metricDifferential_apply]
  rw [← connectionBilinear_apply, ← connectionBilinear_apply,
    ← metricBilinear_apply, ← metricBilinear_apply]
  rw [← axis_expansion a, ← axis_expansion u, ← axis_expansion v]
  simp only [map_sum, map_smul, _root_.sum_apply, _root_.smul_apply, smul_eq_mul, Finset.mul_sum]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hs :
      (∑ j, ∑ l, v i * (a j * (u l * metricBilinear g x (axis l)
        (connectionBilinear g x (axis j) (axis i))))) =
      (∑ j, ∑ l, v i * (a l * (u j * metricBilinear g x (axis j)
        (connectionBilinear g x (axis l) (axis i))))) := Finset.sum_comm
  simp only [Finset.mul_sum, hs, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun l _ => ?_
  have h := congrArg (fun t => u j * a l * v i * t) (hb l j i)
  nlinarith only [h]

/-- The derivative of a metric pairing along a curve uses the same
coordinate connection as the normal-coordinate geodesic IVP. -/
theorem hasDerivAt_metricPair {U : Set (X dim)} (hU : IsOpen U) {g : (MetricField dim)}
    (hg : SmoothMetric U g) {q u v : ℝ → (X dim)} {a b c : (X dim)} {t : ℝ}
    (hqt : q t ∈ U) (hq : HasDerivAt q a t) (hu : HasDerivAt u b t) (hv : HasDerivAt v c t) :
    HasDerivAt (fun s => metricPair g (q s) (u s) (v s))
      (metricPair g (q t) (b + connection g (q t) a (u t)) (v t) +
        metricPair g (q t) (u t) (c + connection g (q t) a (v t))) t := by
  have h₁ (i j : (I dim)) :
      HasDerivAt (fun s => g (q s) i j) (fderiv ℝ (fun y => g y i j) (q t) a) t :=
    (((hg.1 i j).contDiffAt (hU.mem_nhds hqt)).differentiableAt (by simp)).hasFDerivAt.comp_hasDerivAt t hq
  have h₂ (i : (I dim)) : HasDerivAt (fun s => u s i) (b i) t :=
    (EuclideanSpace.proj i : (X dim) →L[ℝ] ℝ).hasFDerivAt.comp_hasDerivAt t hu
  have h₃ (j : (I dim)) : HasDerivAt (fun s => v s j) (c j) t :=
    (EuclideanSpace.proj j : (X dim) →L[ℝ] ℝ).hasFDerivAt.comp_hasDerivAt t hv
  have h : HasDerivAt (fun s => metricPair g (q s) (u s) (v s))
      (∑ i : (I dim), ∑ j : (I dim), (((fderiv ℝ (fun y => g y i j) (q t) a) * u t i + g (q t) i j * b i) * v t j +
        g (q t) i j * u t i * c j)) t := by
    have h0 := HasDerivAt.fun_sum (u := (Finset.univ : Finset (I dim))) (fun i _ =>
      HasDerivAt.fun_sum (u := (Finset.univ : Finset (I dim))) (fun j _ => ((h₁ i j).mul (h₂ i)).mul (h₃ j)))
    exact h0
  convert h using 1
  have hComp := directional_metric_compatibility hU hg hqt a (u t) (v t)
  simp only [metricPair, PiLp.add_apply, add_mul, mul_add, Finset.sum_add_distrib, Pi.mul_apply] at hComp ⊢
  linear_combination -hComp

/-- The geodesic equation preserves the squared speed in the metric. -/
theorem hasDerivAt_geodesic_squaredSpeed_zero {U : Set (X dim)} (hU : IsOpen U) {g : (MetricField dim)}
    (hg : SmoothMetric U g) {q v : ℝ → (X dim)} {t : ℝ} (hqt : q t ∈ U)
    (hq : HasDerivAt q (v t) t)
    (hv : HasDerivAt v (-connection g (q t) (v t) (v t)) t) :
    HasDerivAt (fun s => metricPair g (q s) (v s) (v s)) 0 t := by
  simpa only [neg_add_cancel,metricPair,PiLp.zero_apply,mul_zero,zero_mul,Finset.sum_const_zero,
    add_zero] using hasDerivAt_metricPair hU hg hqt hq hv hv

end CalderonN
