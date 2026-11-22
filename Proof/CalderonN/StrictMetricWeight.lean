module

public import Proof.CalderonN.CovariantHessian
public import Proof.CalderonN.MetricVolumeDifferential

import Proof.CalderonN.StrictMetricHessian
import Proof.CalderonN.StrictParametricPoint
import Proof.CalderonN.ChartBilinear
import Proof.CalderonN.MetricDivergence
import Proof.CalderonN.MetricCalculus
import Proof.CalderonN.MetricPair
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Tactic

@[expose] public section

noncomputable section
open Set Metric MeasureTheory
open scoped ContDiff BigOperators

namespace CalderonN

variable {dim : ℕ} [NeZero dim]
open Elliptic.Strict (JointSmooth jointSmooth_slice)

@[expose] def chartMetricGradient (g : (MetricField dim)) (φ : (X dim) → ℝ) (x : (X dim)) : (X dim) :=
  WithLp.toLp 2 fun i => ∑ j, (g x)⁻¹ i j * coordDeriv j φ x

@[expose] def metricHessianEval (g : (MetricField dim)) (φ : (X dim) → ℝ) (x : (X dim)) (v w : (X dim)) : ℝ :=
  ∑ i, ∑ j, metricHessian g φ x i j * v i * w j

theorem metricHessianEval_eq_fderiv (g : (MetricField dim)) {φ : (X dim) → ℝ} {x : (X dim)}
    {D : (X dim) →L[ℝ] (X dim) →L[ℝ] ℝ} (hD : HasFDerivAt (fderiv ℝ φ) D x) (v w : (X dim)) :
    metricHessianEval g φ x v w = D v w -
      fderiv ℝ φ x (connection g x v w) := by
  have hsecond (i j : (I dim)) : coordDeriv i (coordDeriv j φ) x = D (axis i) (axis j) := by
    let L := ContinuousLinearMap.apply ℝ ℝ (axis j)
    have h := L.hasFDerivAt.comp x hD
    change fderiv ℝ (L ∘ fderiv ℝ φ) x (axis i) = _
    rw [h.fderiv]
    rfl
  let L := (ContinuousLinearMap.apply ℝ ℝ w).comp D
  have hL : L v = D v w := rfl
  have hsum : D v w = ∑ i, ∑ j, D (axis i) (axis j) * v i * w j := by
    rw [← hL,covector_axis_sum L v]
    apply Finset.sum_congr rfl
    intro i _
    change (D (axis i) w) * v i = _
    rw [covector_axis_sum (D (axis i)) w,dotProduct,Finset.sum_mul]
    exact Finset.sum_congr rfl fun j _ => by ring
  rw [metricHessianEval,hsum,covector_axis_sum (fderiv ℝ φ x) (connection g x v w)]
  simp only [metricHessian,hessian,hsecond]
  simp only [coordDeriv, connection, PiLp.toLp_apply, dotProduct, sub_mul,
    Finset.sum_sub_distrib, Finset.sum_mul, Finset.mul_sum]
  congr 1
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  conv_rhs => rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => by ring

/-- The strict Hessian condition for a single actual chart metric. -/
@[expose] def StrictMetricWeightAt (g : (MetricField dim)) (φ : (X dim) → ℝ) (x : (X dim)) : Prop :=
  (fun i => coordDeriv i φ x) ≠ 0 ∧
    ∀ v : (X dim), metricPair g x v v = 1 → metricPair g x (chartMetricGradient g φ x) v = 0 →
      0 < metricHessianEval g φ x (chartMetricGradient g φ x) (chartMetricGradient g φ x) /
        covectorSq g φ x + metricHessianEval g φ x v v

open Carleman Carleman.Strict in
private theorem christoffelHess_eq_metricHessian (g : (MetricField dim)) (φ : (X dim) → ℝ) (x : (X dim))
    (hg : ∀ y, (g y).PosDef) (i j : (I dim)) :
    christoffelHess (fun a b y => g y a b) (fun a b y => (g y)⁻¹ a b) φ x i j =
      metricHessian g φ x i j := by
  have hsym (a b : (I dim)) : (fun y => g y a b) = fun y => g y b a := by
    funext y
    exact congrFun (congrFun (hg y).isHermitian.isSymm.eq b) a
  simp only [christoffelHess, metricHessian, hessian]
  change coordDeriv i (coordDeriv j φ) x - _ = _
  congr 1
  apply Finset.sum_congr rfl
  intro k _
  congr 1
  simp only [christoffel, hsym j]
  simp only [Carleman.pd, coordDeriv, axis, Finset.mul_sum, div_eq_mul_inv,
    Finset.sum_mul]
  exact Finset.sum_congr rfl fun l _ => by ring

open Carleman Carleman.Strict in
private theorem point_strictness_chart {g : (MetricField dim)} (hg : SmoothMetric univ g)
    {φ : (X dim) → ℝ} (hφ : ContDiff ℝ ∞ φ) {x : (X dim)} (h : StrictMetricWeightAt g φ x) :
    let b := fun i j y => divergenceCoeff g y i j
    0 < phaseNorm b φ x ∧
      ∀ ξ : (I dim) → ℝ, ξ ≠ 0 → ∑ j, phaseField b φ j x * ξ j = 0 →
        0 < Mgrad b (phaseField b φ) x ξ +
          4 * ((∑ j, phaseField b φ j x * pd j (phaseNorm b φ) x) / (2 * phaseNorm b φ x)) *
            quad b x ξ := by
  let A := fun (i j : (I dim)) (y : (X dim)) => (g y)⁻¹ i j
  let G := fun (i j : (I dim)) (y : (X dim)) => g y i j
  have hA (i j : (I dim)) : ContDiff ℝ ∞ (A i j) := contDiffOn_univ.mp (contDiffOn_metric_inv_entry hg i j)
  have hA_symm (i j : (I dim)) : A i j = A j i := by
    funext z
    exact congrFun (congrFun (hg.2 z (mem_univ z)).inv.isHermitian.isSymm.eq j) i
  have hder (r i j : (I dim)) : pd r (A i j) x = -∑ s, ∑ t, A i s x * pd r (G s t) x * A t j x :=
    fderiv_inverseMetric_entry_apply g x (axis r)
      (fun a b => (contDiffOn_univ.mp (hg.1 a b)).differentiable (by simp) x)
      (hg.2 x (mem_univ x)) i j
  have hGA (i j : (I dim)) : ∑ k, G i k x * A k j x = if i = j then 1 else 0 := by
    have hm := Matrix.mul_nonsing_inv (g x) (isUnit_iff_ne_zero.mpr (hg.2 x (mem_univ x)).det_pos.ne')
    exact (congrFun (congrFun hm i) j).trans Matrix.one_apply
  have hpositive (v : (I dim) → ℝ) (hv : v ≠ 0) : 0 < ∑ i, ∑ j, G i j x * v i * v j :=
    metricPair_pos_of_posDef (hg.2 x (mem_univ x)) (v := WithLp.toLp 2 v) (by
      intro hzero
      apply hv
      exact congrArg WithLp.ofLp hzero)
  have hhess (i j : (I dim)) : christoffelHess G A φ x i j = metricHessian g φ x i j :=
    christoffelHess_eq_metricHessian g φ x (fun y => hg.2 y (mem_univ y)) i j
  have hs := point_criterion_of_metric_strictness (G := G) hA hφ hA_symm x hder hGA hpositive h.1
    (fun v hv horth => by
      simp only [hhess]
      exact h.2 (WithLp.toLp 2 v) hv horth)
  exact point_strictness_smul (fun _ _ _ => rfl)
    (contDiffOn_univ.mp (contDiffOn_metric_volume hg)) hA hφ x
    (Real.sqrt_pos.mpr (hg.2 x (mem_univ x)).det_pos) hs.1 hs.2

open Carleman Carleman.Strict in
/-- The unchanged Carleman weight on the actual chart Laplacian.
Uniformity is joint in the metric and weight parameters near the strict point. -/
theorem exists_local_metricCarleman {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
    [FiniteDimensional ℝ P] {g : P → (MetricField dim)} {φ : P → (X dim) → ℝ}
    (hg : ∀ i j, ContDiff ℝ ∞ (fun q : P × (X dim) => g q.1 q.2 i j))
    (hp : ∀ a x, (g a x).PosDef)
    (hφ : ContDiff ℝ ∞ (fun q : P × (X dim) => φ q.1 q.2))
    (a₀ : P) (x₀ : (X dim)) (hs : StrictMetricWeightAt (g a₀) (φ a₀) x₀) :
    ∃ r C τ₀ : ℝ, 0 < r ∧ 0 < C ∧ 1 ≤ τ₀ ∧
      ∀ a ∈ closedBall a₀ r, ∀ τ : ℝ, τ₀ ≤ τ →
      ∀ w : (X dim) → ℝ, ContDiff ℝ ∞ w → HasCompactSupport w → tsupport w ⊆ closedBall x₀ r →
        τ * (∫ x, ∑ i, coordDeriv i (fun y => Real.exp (τ * φ a y) * w y) x ^ 2) +
        τ^3 * (∫ x, (Real.exp (τ * φ a x) * w x)^2) ≤
          C * ∫ x, Real.exp (2*(τ * φ a x)) * (chartVolume (g a) x * laplace (g a) w x)^2 := by
  let b := fun a i j y => divergenceCoeff (g a) y i j
  have hbg : ∀ i j, JointSmooth (fun a => b a i j) := by
    let G (q : P × (X dim)) := g q.1 q.2
    have hG : ∀ i j, ContDiffOn ℝ ∞ (fun q => G q i j) univ := fun i j => (hg i j).contDiffOn
    have hd : ContDiffOn ℝ ∞ (fun q : P × (X dim) => Real.sqrt (G q).det) univ :=
      (contDiffOn_det_of_entries hG).sqrt (fun q _ => (hp q.1 q.2).det_pos.ne')
    intro i j
    exact contDiffOn_univ.mp (hd.mul
      (contDiffOn_inv_entry_of_entries hG (fun q _ => (hp q.1 q.2).det_pos.ne') i j))
  have hgs (a : P) : SmoothMetric univ (g a) :=
    ⟨fun i j => ((hg i j).comp (contDiff_const.prodMk contDiff_id)).contDiffOn, fun x _ => hp a x⟩
  have hsym (a : P) (i j : (I dim)) : b a i j = b a j i :=
    funext fun y => divergenceCoeff_symm (hgs a) (mem_univ y) i j
  have hstrict := point_strictness_chart (hgs a₀) (jointSmooth_slice hφ a₀) hs
  obtain ⟨r, C, τ₀, hr, hC, hτ, hEst⟩ := exists_local_parameter_strict_weight_carleman_of_point_criterion
    b φ hbg hφ hsym a₀ x₀ hstrict.1 hstrict.2
  refine ⟨r,C,τ₀,hr,hC,hτ, fun a ha τ ht w hw hwc hsupp => ?_⟩
  have he (x : (X dim)) : Lop (b a) w x = chartVolume (g a) x * laplace (g a) w x :=
    (chartVolume_mul_laplace_eq_divergence isOpen_univ (hgs a) hw.contDiffOn (mem_univ x)).symm
  simpa only [he, pd, coordDeriv, axis] using hEst a ha τ ht w hw hwc hsupp

end CalderonN
