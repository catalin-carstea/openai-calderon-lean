module

public import Proof.CalderonN.FrameOperators
public import Proof.CalderonN.ProductPhaseAlgebra

import Proof.CalderonN.MetricPair
import Proof.CalderonN.ChartBilinear
import Mathlib.Tactic

@[expose] public section

noncomputable section
open scoped InnerProductSpace

namespace CalderonN

variable {dim : ℕ} [NeZero dim]

/-- The normalized gradient and the equal-length tangent condition can be
read in the reference frame using its inverse and covariant metric operators. -/
theorem framed_normalizedGradient_and_tangent
    (γ g : (MetricField dim)) (y : (X dim)) (e : (I dim) → (X dim))
    (he : ∀ i j, metricPair γ y (e i) (e j) = if i = j then 1 else 0)
    (hg : (g y).PosDef) (f : (X dim) → ℝ) (n : (X dim)) {r : ℝ} (hr : r ≠ 0)
    (hf : ∀ v : (X dim), fderiv ℝ f y v = r * ⟪n,frameCoordinatesL γ y e v⟫_ℝ) :
    let S := frameCoordinatesL γ y e
    let A := frameMetricOperator (g y) e
    let Q := frameCometricOperator γ y e (g y)⁻¹
    let a := (covectorSq g f y)⁻¹ • chartMetricGradient g f y
    r • S a = (⟪n,Q n⟫_ℝ)⁻¹ • Q n ∧
      (∀ v : (X dim), metricPair g y (chartMetricGradient g f y) v = 0 →
        metricPair g y v v = metricPair g y a a →
        let U := r • S v
        ⟪n,U⟫_ℝ = 0 ∧ ⟪U,A U⟫_ℝ = (⟪n,Q n⟫_ℝ)⁻¹) := by
  let S := frameCoordinatesL γ y e
  let A := frameMetricOperator (g y) e
  let Q := frameCometricOperator γ y e (g y)⁻¹
  let a := (covectorSq g f y)⁻¹ • chartMetricGradient g f y
  let d := chartMetricGradient g f y
  let c := ⟪n,Q n⟫_ℝ
  have hd (v : (X dim)) : metricPair g y d v = r * ⟪n,S v⟫_ℝ := by
    rw [← hf,metricPair_metricGradient _ _ _ _ hg]
    exact (covector_axis_sum (fderiv ℝ f y) v).symm
  have hMetric (v w : (X dim)) : ⟪S v,A (S w)⟫_ℝ = metricPair g y v w := by
    rw [inner_frameMetricOperator,frameVectorL_frameCoordinatesL γ y e he,
      frameVectorL_frameCoordinatesL γ y e he]
  have hA : A (S d) = r • n := by
    apply ext_inner_left ℝ
    intro v
    rw [← frameCoordinatesL_frameVectorL γ y e he v,hMetric,metricPair_comm hg _ d,
      hd,frameCoordinatesL_frameVectorL γ y e he,real_inner_smul_right,real_inner_comm n]
  have hS : S d = r • Q n := by
    have h := congrArg Q hA
    rw [frameCometricOperator_frameMetricOperator γ y e he _ hg,map_smul] at h
    exact h
  have hnd : covectorSq g f y = r^2*c := by
    rw [← metricPair_gradient_self _ _ _ hg,hd,hS,real_inner_smul_right]
    dsimp [c]
    ring
  have hq : r • S a = c⁻¹ • Q n := by
    change r • S ((covectorSq g f y)⁻¹ • d) = _
    rw [map_smul,hS,hnd]
    simp only [smul_smul,_root_.mul_inv_rev]
    have he : r * (c⁻¹ * (r^2)⁻¹ * r) = c⁻¹ := by
      rw [show r * (c⁻¹ * (r^2)⁻¹ * r) = c⁻¹ * (r^2 * (r^2)⁻¹) by ring,
        mul_inv_cancel₀ (pow_ne_zero _ hr),mul_one]
    rw [he]
  refine ⟨hq,fun v hv hvlen => ?_⟩
  have hOrth : r * ⟪n,S v⟫_ℝ = 0 := (hd v).symm.trans hv
  have hpos : ⟪r • S a,A (r • S a)⟫_ℝ = c⁻¹ := by
    rw [hq,map_smul,real_inner_smul_left,real_inner_smul_right]
    have hAv : A (Q n) = n := by
      have h : A (r • Q n) = r • n := hS ▸ hA
      rw [map_smul] at h
      exact (smul_right_injective (X dim) hr) h
    rw [hAv,real_inner_comm n (Q n)]
    change c⁻¹ * (c⁻¹ * c) = c⁻¹
    by_cases hc : c = 0
    · simp [hc]
    · rw [inv_mul_cancel₀ hc,mul_one]
  refine ⟨by rw [real_inner_smul_right,hOrth],?_⟩
  have hscale (w : (X dim)) : ⟪r • S w,A (r • S w)⟫_ℝ = r * (r * metricPair g y w w) := by
    rw [map_smul A r (S w),real_inner_smul_left,real_inner_smul_right,hMetric]
  calc
    ⟪r • S v,A (r • S v)⟫_ℝ = r * (r * metricPair g y v v) := hscale v
    _ = r * (r * metricPair g y a a) := by rw [hvlen]
    _ = ⟪r • S a,A (r • S a)⟫_ℝ := (hscale a).symm
    _ = c⁻¹ := hpos

end CalderonN
