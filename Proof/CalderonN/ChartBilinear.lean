module

public import Proof.CalderonN.Chart
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.LinearAlgebra.Matrix.BilinearForm

import Mathlib.Algebra.Order.Star.Real
import Mathlib.Tactic

@[expose] public section

noncomputable section
open Set Matrix

namespace CalderonN

variable {dim : ℕ}

abbrev chartCoordBasis (dim : ℕ) := (EuclideanSpace.basisFun (I dim) ℝ).toBasis

/-- The real bilinear form in the protected coordinate axes. -/
@[expose] def chartBilinear (M : (Mat dim)) : (X dim) →L[ℝ] (X dim) →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap
    ((LinearMap.toContinuousLinearMap : ((X dim) →ₗ[ℝ] ℝ) ≃ₗ[ℝ] ((X dim) →L[ℝ] ℝ)).toLinearMap.comp
      (Matrix.toBilin (chartCoordBasis dim) M))

theorem chartBilinear_apply (M : (Mat dim)) (v w : (X dim)) :
    chartBilinear M v w = (fun i => v i) ⬝ᵥ (M *ᵥ (fun j => w j)) := by
  change Matrix.toBilin (chartCoordBasis dim) M v w = _
  simp only [Matrix.toBilin_apply, chartCoordBasis, OrthonormalBasis.coe_toBasis_repr_apply,
    EuclideanSpace.basisFun_repr, dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc]

theorem chartBilinear_axis (M : (Mat dim)) (i j : (I dim)) :
    chartBilinear M (axis i) (axis j) = M i j := by
  change Matrix.toBilin (chartCoordBasis dim) M (axis i) (axis j) = _
  rw [show axis i = (chartCoordBasis dim) i from (EuclideanSpace.basisFun_apply (I dim) ℝ i).symm,
    show axis j = (chartCoordBasis dim) j from (EuclideanSpace.basisFun_apply (I dim) ℝ j).symm,
    Matrix.toBilin_apply]
  simp only [Module.Basis.repr_self, Finsupp.single_apply, Finset.sum_ite_eq, Finset.mem_univ, ite_true, mul_ite, ite_mul, zero_mul, mul_zero, one_mul, mul_one]

theorem chartBilinear_symm {M : (Mat dim)} (hM : M.IsHermitian) (v w : (X dim)) :
    chartBilinear M v w = chartBilinear M w v := by
  rw [chartBilinear_apply, chartBilinear_apply, dotProduct_mulVec, ← mulVec_transpose]
  rw [hM.isSymm.eq, dotProduct_comm]

/-- A coordinate covector evaluated on the Christoffel correction. -/
theorem covector_connection_eq_bilinear (g : (MetricField dim)) (x v w : (X dim)) (d : (X dim) →L[ℝ] ℝ) :
    d (connection g x v w) =
      chartBilinear (fun i j => ∑ k, d (axis k) * christoffel g x k i j) v w := by
  have hrepr (q : (X dim)) : d q = ∑ k, d (axis k) * q k := by
    have ht := congrArg d ((chartCoordBasis dim).sum_repr q).symm
    simpa only [map_sum, map_smul, smul_eq_mul, chartCoordBasis, OrthonormalBasis.coe_toBasis_repr_apply,
      EuclideanSpace.basisFun_repr, OrthonormalBasis.coe_toBasis, EuclideanSpace.basisFun_apply,
      axis, mul_comm] using ht
  rw [hrepr]
  have h := chartBilinear_apply (fun i j => ∑ k, d (axis k) * christoffel g x k i j) v w
  rw [h]
  simp only [connection, PiLp.toLp_apply, Matrix.mulVec, dotProduct, Finset.mul_sum,
    Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => by ring

theorem christoffel_symm_of_smoothMetric {g : (MetricField dim)} (hg : SmoothMetric univ g)
    (x : (X dim)) (k i j : (I dim)) :
    christoffel g x k i j = christoffel g x k j i := by
  have hs (a b : (I dim)) : (fun y => g y a b) = fun y => g y b a :=
    funext fun y => congrFun (congrFun (hg.2 y (mem_univ y)).isHermitian.isSymm.eq b) a
  simp only [christoffel]
  congr 1
  exact Finset.sum_congr rfl fun l _ => by rw [hs l j, hs i l, hs i j]; ring

theorem connection_symm_of_smoothMetric {g : (MetricField dim)} (hg : SmoothMetric univ g) (x v w : (X dim)) :
    connection g x v w = connection g x w v := by
  ext k
  simp only [connection, PiLp.toLp_apply]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by
    rw [christoffel_symm_of_smoothMetric hg x k i j]
    ring

theorem covector_axis_sum (d : (X dim) →L[ℝ] ℝ) (v : (X dim)) :
    d v = (fun i => d (axis i)) ⬝ᵥ (fun i => v i) := by
  have ht := congrArg d ((chartCoordBasis dim).sum_repr v).symm
  simpa only [dotProduct, map_sum, map_smul, smul_eq_mul, chartCoordBasis, OrthonormalBasis.coe_toBasis_repr_apply,
    EuclideanSpace.basisFun_repr, OrthonormalBasis.coe_toBasis, EuclideanSpace.basisFun_apply,
    axis, mul_comm] using ht

end CalderonN
