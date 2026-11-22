module

public import Proof.CalderonN.StrictMetricWeight
public import Proof.CalderonN.ProductHessian.Separation

import Proof.CalderonN.MetricPair
import Proof.CalderonN.SphereFrame
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Tactic

@[expose] public section

noncomputable section
open Set Matrix
open scoped ContDiff

namespace CalderonN

variable {dim : ℕ} [NeZero dim]

theorem metricPair_metricGradient (g : (MetricField dim)) (f : (X dim) → ℝ) (x v : (X dim))
    (hg : (g x).PosDef) :
    metricPair g x (chartMetricGradient g f x) v = (fun i => coordDeriv i f x) ⬝ᵥ (fun i => v i) := by
  let d (i : (I dim)) := coordDeriv i f x
  have hinv : ((g x)⁻¹)ᵀ = (g x)⁻¹ := hg.inv.isHermitian.isSymm.eq
  have hmat : (g x) * (g x)⁻¹ = 1 := Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hg.det_pos.ne')
  rw [metricPair_eq_dotProduct]
  change ((g x)⁻¹ *ᵥ d) ⬝ᵥ (g x *ᵥ (fun i => v i)) = d ⬝ᵥ (fun i => v i)
  rw [Matrix.dotProduct_mulVec, Matrix.vecMul_mulVec, ← Matrix.mulVec_transpose, hinv,
    Matrix.transpose_mul, hg.isHermitian.isSymm.eq, hinv, hmat, Matrix.one_mulVec]

theorem metricPair_gradient_self (g : (MetricField dim)) (f : (X dim) → ℝ) (x : (X dim)) (hg : (g x).PosDef) :
    metricPair g x (chartMetricGradient g f x) (chartMetricGradient g f x) = covectorSq g f x := by
  rw [metricPair_metricGradient g f x _ hg]
  simp only [chartMetricGradient, PiLp.toLp_apply, covectorSq, dotProduct, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

theorem metricHessianEval_smul_same (g : (MetricField dim)) (f : (X dim) → ℝ) (x v : (X dim)) (c : ℝ) :
    metricHessianEval g f x (c • v) (c • v) = c^2 * metricHessianEval g f x v v := by
  simp only [metricHessianEval, PiLp.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

/-- Chart form of the identity (d f(a) = 1) for (a=
abla f/|d f|^2). -/
theorem normalizedGradient_pair (g : (MetricField dim)) (f : (X dim) → ℝ) (x : (X dim))
    (hg : (g x).PosDef) (hd : (fun i => coordDeriv i f x) ≠ 0) :
    let a := (covectorSq g f x)⁻¹ • chartMetricGradient g f x
    (fun i => coordDeriv i f x) ⬝ᵥ (fun i => a i) = 1 := by
  intro a
  have hN : 0 < covectorSq g f x := by
    obtain ⟨i,hi⟩ : ∃ i, coordDeriv i f x ≠ 0 := by
      by_contra! h
      exact hd (funext h)
    exact covectorSq_pos hg hi
  rw [← metricPair_metricGradient g f x a hg]
  change metricPair g x (chartMetricGradient g f x) ((covectorSq g f x)⁻¹ • chartMetricGradient g f x) = _
  rw [metricPair_smul_right, metricPair_gradient_self g f x hg, inv_mul_cancel₀ hN.ne']

theorem metricHessianEval_eq_matrix (g : (MetricField dim)) (f : (X dim) → ℝ) (x v w : (X dim)) :
    metricHessianEval g f x v w = (fun i => v i) ⬝ᵥ
      ((fun i j => metricHessian g f x i j : (Mat dim)) *ᵥ (fun i => w i)) := by
  simp only [metricHessianEval, Matrix.mulVec, dotProduct, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

/-- The matrix separation cone becomes the source unit tangential strictness
when the prescribed covector and covariant Hessian are realized by a phase. -/
theorem strictMetricWeightAt_of_matrix_cone
    {g : (MetricField dim)} {f : (X dim) → ℝ} {x : (X dim)}
    (hg : (g x).PosDef) (hd : (fun i => coordDeriv i f x) ≠ 0)
    (P : selfAdjoint (Mat dim)) (hP : ∀ i j, metricHessian g f x i j = (P : (Mat dim)) i j)
    (hcone : P ∈ ProductHessianSeparation.strictSphereCone (g x) (fun i => coordDeriv i f x)
      (fun i => ((covectorSq g f x)⁻¹ • chartMetricGradient g f x : (X dim)) i)) :
    StrictMetricWeightAt g f x := by
  let n := covectorSq g f x
  let b := chartMetricGradient g f x
  let a : (X dim) := n⁻¹ • b
  have hn : 0 < n := by
    obtain ⟨i,hi⟩ : ∃ i, coordDeriv i f x ≠ 0 := by
      by_contra! h
      exact hd (funext h)
    exact covectorSq_pos hg hi
  let t : ℝ := (Real.sqrt n)⁻¹
  have ht : 0 < t := inv_pos.mpr (Real.sqrt_pos.mpr hn)
  have htn : t^2 = n⁻¹ := by rw [show t = (Real.sqrt n)⁻¹ from rfl, inv_pow, Real.sq_sqrt hn.le]
  have ha : metricPair g x a a = t^2 := by
    rw [show a = n⁻¹ • b from rfl, metricPair_smul_same, metricPair_gradient_self g f x hg, htn]
    change n⁻¹ ^ 2 * n = n⁻¹
    field_simp
  refine ⟨hd, fun v hv hvorth => ?_⟩
  let w : (X dim) := t • v
  have hworth : (fun i => coordDeriv i f x) ⬝ᵥ (fun i => w i) = 0 := by
    rw [← metricPair_metricGradient _ _ _ _ hg, show w = t • v from rfl, metricPair_smul_right, hvorth, mul_zero]
  have hwnorm : metricPair g x w w = metricPair g x a a := by
    rw [show w = t • v from rfl, metricPair_smul_same, hv, mul_one, ha]
  have hw : (fun i => w i) ∈ ProductHessianSeparation.metricTangentSphere (g x)
      (fun i => coordDeriv i f x) (fun i => a i) := by
    refine ⟨hworth, ?_⟩
    simpa only [metricPair_eq_dotProduct] using hwnorm
  have hForm : (fun i j => metricHessian g f x i j : (Mat dim)) = (P : (Mat dim)) := funext fun i => funext fun j => hP i j
  have hpos : 0 < metricHessianEval g f x a a + metricHessianEval g f x w w := by
    simp only [metricHessianEval_eq_matrix, hForm]
    exact hcone _ hw
  rw [show a = n⁻¹ • b from rfl, show w = t • v from rfl,
    metricHessianEval_smul_same, metricHessianEval_smul_same, htn] at hpos
  change 0 < metricHessianEval g f x b b / n + metricHessianEval g f x v v
  have he :
      n⁻¹ ^ 2 * metricHessianEval g f x b b + n⁻¹ * metricHessianEval g f x v v =
        n⁻¹ * (metricHessianEval g f x b b / n + metricHessianEval g f x v v) := by
    rw [div_eq_mul_inv]
    ring
  rw [he] at hpos
  exact pos_of_mul_pos_right hpos (inv_pos.mpr hn).le

end CalderonN
