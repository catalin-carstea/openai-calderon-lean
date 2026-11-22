module

public import Proof.CalderonN.Chart

import Proof.CalderonN.ChartGeometry
import Proof.CalderonN.MetricCalculus
import Mathlib.Tactic.Ring

@[expose] public section

noncomputable section
open Set Matrix
open scoped BigOperators ContDiff

namespace CalderonN

variable {dim : ℕ}

@[expose] def metricHessian (g : (MetricField dim)) (f : (X dim) → ℝ) (y : (X dim)) (i j : (I dim)) : ℝ :=
  hessian f y i j - ∑ k, christoffel g y k i j * coordDeriv k f y

@[expose] def covectorSq (g : (MetricField dim)) (f : (X dim) → ℝ) (y : (X dim)) : ℝ :=
  ∑ i, ∑ j, (g y)⁻¹ i j * coordDeriv i f y * coordDeriv j f y

theorem covJet_two_eq_metricHessian (g : (MetricField dim)) (f : (X dim) → ℝ) (y : (X dim)) (i j : (I dim)) :
    covJet g f 2 y ![i, j] = metricHessian g f y i j := by
  simp only [covJet, Finset.univ_eq_empty, Finset.sum_empty, sub_zero, Fin.sum_univ_one,
    Matrix.cons_val_zero, Fin.tail_def, Function.update_self, Fin.succ_zero_eq_one,
    Matrix.cons_val_one, metricHessian, hessian]

theorem contDiffOn_christoffel {U : Set (X dim)} (hU : IsOpen U) {g : (MetricField dim)}
    (hg : SmoothMetric U g) (k i j : (I dim)) : ContDiffOn ℝ ∞ (fun y => christoffel g y k i j) U := by
  unfold christoffel
  refine (ContDiffOn.sum fun l _ => (contDiffOn_metric_inv_entry hg k l).mul ?_).div_const _
  exact ((contDiffOn_coordDeriv (hg.1 l j) hU i).add (contDiffOn_coordDeriv (hg.1 i l) hU j)).sub
    (contDiffOn_coordDeriv (hg.1 i j) hU l)

theorem contDiffOn_metricHessian {U : Set (X dim)} (hU : IsOpen U) {g : (MetricField dim)}
    (hg : SmoothMetric U g) {f : (X dim) → ℝ} (hf : ContDiffOn ℝ ∞ f U) (i j : (I dim)) :
    ContDiffOn ℝ ∞ (fun y => metricHessian g f y i j) U :=
  (contDiffOn_coordDeriv (contDiffOn_coordDeriv hf hU j) hU i).sub
    (ContDiffOn.sum fun k _ => (contDiffOn_christoffel hU hg k i j).mul (contDiffOn_coordDeriv hf hU k))

theorem contDiffOn_covectorSq {U : Set (X dim)} (hU : IsOpen U) {g : (MetricField dim)}
    (hg : SmoothMetric U g) {f : (X dim) → ℝ} (hf : ContDiffOn ℝ ∞ f U) :
    ContDiffOn ℝ ∞ (covectorSq g f) U :=
  ContDiffOn.sum fun i _ => ContDiffOn.sum fun j _ =>
    ((contDiffOn_metric_inv_entry hg i j).mul (contDiffOn_coordDeriv hf hU i)).mul
      (contDiffOn_coordDeriv hf hU j)

theorem covectorSq_pos {g : (MetricField dim)} {f : (X dim) → ℝ} {y : (X dim)} (hg : (g y).PosDef)
    {k : (I dim)} (hk : coordDeriv k f y ≠ 0) : 0 < covectorSq g f y := by
  let d (i : (I dim)) := coordDeriv i f y
  have hd : d ≠ 0 := fun h => hk (congrFun h k)
  have he : covectorSq g f y = d ⬝ᵥ ((g y)⁻¹ *ᵥ d) := by
    simp only [covectorSq, Matrix.mulVec, dotProduct, Finset.mul_sum]
    apply Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    dsimp only [d]
    ring
  rw [he]
  exact hg.inv.dotProduct_mulVec_pos hd

theorem coordDeriv_scalar_comp {f : (X dim) → ℝ} {F : ℝ → ℝ} {x : (X dim)}
    (hf : DifferentiableAt ℝ f x) {a : ℝ} (hF : HasDerivAt F a (f x)) (i : (I dim)) :
    coordDeriv i (F ∘ f) x = a * coordDeriv i f x := by
  have hc := hF.hasFDerivAt.comp x hf.hasFDerivAt
  simp only [coordDeriv, hc.fderiv, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.toSpanSingleton_apply, smul_eq_mul, mul_comm]

theorem metricHessian_scalar_comp {U : Set (X dim)} (hU : IsOpen U)
    (g : (MetricField dim)) {f : (X dim) → ℝ} (hf : ContDiffOn ℝ ∞ f U) {F F' : ℝ → ℝ}
    (hF : ∀ t, HasDerivAt F (F' t) t) {x : (X dim)} (hx : x ∈ U) {a : ℝ}
    (ha : HasDerivAt F' a (f x)) (i j : (I dim)) :
    metricHessian g (F ∘ f) x i j =
      F' (f x) * metricHessian g f x i j + a * coordDeriv i f x * coordDeriv j f x := by
  have hdf (z : (X dim)) (hz : z ∈ U) :=
    (hf.differentiableOn (by simp)).differentiableAt (hU.mem_nhds hz)
  have heq (k : (I dim)) (z : (X dim)) (hz : z ∈ U) :
      coordDeriv k (F ∘ f) z = F' (f z) * coordDeriv k f z :=
    coordDeriv_scalar_comp (hdf z hz) (hF (f z)) k
  have hdiff : DifferentiableAt ℝ (coordDeriv j f) x :=
    ((contDiffOn_coordDeriv hf hU j).differentiableOn (by simp)).differentiableAt (hU.mem_nhds hx)
  have hDc : DifferentiableAt ℝ (fun z => F' (f z)) x :=
    ha.differentiableAt.comp x (hdf x hx)
  have he : coordDeriv i (coordDeriv j (F ∘ f)) x =
      a * coordDeriv i f x * coordDeriv j f x + F' (f x) * coordDeriv i (coordDeriv j f) x := by
    rw [eqOn_coordDeriv hU (heq j) i hx]
    have hd : coordDeriv i (fun z => F' (f z) * coordDeriv j f z) x =
        coordDeriv j f x * coordDeriv i (F' ∘ f) x +
          F' (f x) * coordDeriv i (coordDeriv j f) x := by
      change fderiv ℝ (fun z => F' (f z) * coordDeriv j f z) x (axis i) = _
      rw [fderiv_fun_mul hDc hdiff]
      exact add_comm _ _
    rw [hd, coordDeriv_scalar_comp (hdf x hx) ha]
    ring
  unfold metricHessian hessian
  rw [he]
  simp_rw [fun k => heq k x hx, mul_sub, Finset.mul_sum]
  have hh (k : (I dim)) : christoffel g x k i j * (F' (f x) * coordDeriv k f x) =
      F' (f x) * (christoffel g x k i j * coordDeriv k f x) := by ring
  simp only [hh]
  ring

end CalderonN
