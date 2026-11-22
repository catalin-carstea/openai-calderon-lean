module

public import Proof.CalderonN.FramedPhaseNormalization
public import Proof.CalderonN.ProductMetricHessian

import Mathlib.Tactic

@[expose] public section

noncomputable section
open scoped InnerProductSpace

namespace CalderonN

variable {dim : ℕ} [NeZero dim]

/-- The product Hessian evaluated in the two specified endpoint frames. -/
@[expose] def framedProductHessian (γ g : (MetricField dim)) (φ : (X dim) × (X dim) → ℝ)
    (p : (X dim) × (X dim)) (e₁ e₂ : (I dim) → (X dim)) (U V : (X dim)) : ℝ :=
  let v := (frameVectorL e₁ U, frameVectorL e₂ V)
  productMetricHessian γ g φ p v v

private theorem coordDeriv_ne_zero_of_framed_fderiv
    (γ : (MetricField dim)) (y : (X dim)) (e : (I dim) → (X dim))
    (he : ∀ i j, metricPair γ y (e i) (e j) = if i = j then 1 else 0)
    (f : (X dim) → ℝ) (n : (X dim)) (hn : n ≠ 0) {r : ℝ} (hr : r ≠ 0)
    (hf : ∀ v : (X dim), fderiv ℝ f y v = r * ⟪n,frameCoordinatesL γ y e v⟫_ℝ) :
    (fun i => coordDeriv i f y) ≠ 0 := by
  intro h
  have hzero (v : (X dim)) : fderiv ℝ f y v = 0 := by
    rw [covector_axis_sum (fderiv ℝ f y) v]
    have hz (i : (I dim)) : fderiv ℝ f y (axis i) = 0 := congrFun h i
    simp [dotProduct,hz]
  have hd := hf (frameVectorL e n)
  rw [hzero,frameCoordinatesL_frameVectorL γ y e he,real_inner_self_eq_norm_sq] at hd
  exact (mul_ne_zero hr (pow_ne_zero _ (norm_ne_zero_iff.mpr hn))) hd.symm

set_option maxHeartbeats 1000000 in
/-- The strict framed inequality with the two physical normal covectors
implies the literal strict product Hessian test in the chart. -/
theorem productStrictHessianAt_of_framedHessian
    {γ g : (MetricField dim)} {φ : (X dim) × (X dim) → ℝ} {p : (X dim) × (X dim)} (hφ : DifferentiableAt ℝ φ p)
    (e₁ e₂ : (I dim) → (X dim))
    (he₁ : ∀ i j, metricPair γ p.1 (e₁ i) (e₁ j) = if i = j then 1 else 0)
    (he₂ : ∀ i j, metricPair γ p.2 (e₂ i) (e₂ j) = if i = j then 1 else 0)
    (hγ : (γ p.1).PosDef) (hg : (g p.2).PosDef)
    {r : ℝ} (hr : 0 < r) {z n : (X dim)} (hz : ‖z‖ = 1) (hn : n ≠ 0)
    (hfirst : ∀ w : (X dim) × (X dim), fderiv ℝ φ p w = r *
      (⟪z,frameCoordinatesL γ p.1 e₁ w.1⟫_ℝ - ⟪n,frameCoordinatesL γ p.2 e₂ w.2⟫_ℝ))
    (hstrict :
      let R := frameMetricOperator (g p.2) e₂
      let T := frameCometricOperator γ p.2 e₂ (g p.2)⁻¹
      let H := framedProductHessian γ g φ p e₁ e₂
      ∀ U W : (X dim), ⟪z,U⟫_ℝ = 0 → ‖U‖^2 = 1 → ⟪n,W⟫_ℝ = 0 →
        ⟪W,R W⟫_ℝ = (⟪n,T n⟫_ℝ)⁻¹ →
        0 < H z ((⟪n,T n⟫_ℝ)⁻¹ • T n) + H U W) :
    ProductStrictHessianAt γ g φ p := by
  let S₁ := frameCoordinatesL γ p.1 e₁
  let S₂ := frameCoordinatesL γ p.2 e₂
  let f₁ (x : (X dim)) := φ (x,p.2)
  let f₂ (y : (X dim)) := φ (p.1,y)
  let a₁ := (covectorSq γ f₁ p.1)⁻¹ • chartMetricGradient γ f₁ p.1
  let a₂ := (covectorSq g f₂ p.2)⁻¹ • chartMetricGradient g f₂ p.2
  let T := frameCometricOperator γ p.2 e₂ (g p.2)⁻¹
  let H := framedProductHessian γ g φ p e₁ e₂
  obtain ⟨h₁,h₂⟩ := fderiv_product_slices φ p hφ
  have hf₁ (v : (X dim)) : fderiv ℝ f₁ p.1 v = r * ⟪z,S₁ v⟫_ℝ := by
    change fderiv ℝ (fun x => φ (x,p.2)) p.1 v = _
    rw [h₁]
    change fderiv ℝ φ p (v,0) = _
    rw [hfirst]
    simp only [map_zero,inner_zero_right,sub_zero]
    rfl
  have hf₂ (v : (X dim)) : fderiv ℝ f₂ p.2 v = r * ⟪-n,S₂ v⟫_ℝ := by
    change fderiv ℝ (fun y => φ (p.1,y)) p.2 v = _
    rw [h₂]
    change fderiv ℝ φ p (0,v) = _
    rw [hfirst]
    simp only [map_zero,inner_zero_right,zero_sub,inner_neg_left]
    rfl
  have hn₁ : z ≠ 0 := norm_ne_zero_iff.mp (hz.trans_ne one_ne_zero)
  have hf₁ne := coordDeriv_ne_zero_of_framed_fderiv γ p.1 e₁ he₁ f₁ z hn₁ hr.ne' hf₁
  have hf₂ne := coordDeriv_ne_zero_of_framed_fderiv γ p.2 e₂ he₂ f₂ (-n) (neg_ne_zero.mpr hn) hr.ne' hf₂
  refine ⟨hf₁ne,hf₂ne,fun v w hvo hvn hwo hwn => ?_⟩
  have hN₁ := framed_normalizedGradient_and_tangent γ γ p.1 e₁ he₁ hγ f₁ z hr.ne' hf₁
  simp only [frameMetricOperator_ref_eq_id γ p.1 e₁ he₁,
    frameCometricOperator_ref_eq_id γ p.1 e₁ he₁ hγ,ContinuousLinearMap.id_apply,
    real_inner_self_eq_norm_sq,hz,one_pow,inv_one,one_smul] at hN₁
  have hN₂ := framed_normalizedGradient_and_tangent γ g p.2 e₂ he₂ hg f₂ (-n) hr.ne' hf₂
  simp only [map_neg,inner_neg_left,inner_neg_right,neg_neg,neg_eq_zero] at hN₂
  have ha₁ : r • S₁ a₁ = z := hN₁.1
  have ha₂ : r • S₂ (-a₂) = (⟪n,T n⟫_ℝ)⁻¹ • T n := by
    rw [map_neg S₂,smul_neg,hN₂.1,smul_neg,neg_neg]
  have hv := hN₁.2 v hvo hvn
  have hw := hN₂.2 w hwo hwn
  have hSum := hstrict (r • S₁ v) (r • S₂ w) hv.1 hv.2 hw.1 hw.2
  have hScale (u : (X dim) × (X dim)) :
      H (r • S₁ u.1) (r • S₂ u.2) = r^2 * productMetricHessian γ g φ p u u := by
    unfold H framedProductHessian
    rw [map_smul (frameVectorL e₁),map_smul (frameVectorL e₂),
      frameVectorL_frameCoordinatesL γ p.1 e₁ he₁,
      frameVectorL_frameCoordinatesL γ p.2 e₂ he₂]
    exact productMetricHessian_smul_self γ g φ p u r
  change 0 < H z ((⟪n,T n⟫_ℝ)⁻¹ • T n) + H (r • S₁ v) (r • S₂ w) at hSum
  rw [← ha₁,← ha₂, hScale (a₁,-a₂),hScale (v,w),← mul_add] at hSum
  exact (mul_pos_iff_of_pos_left (sq_pos_of_pos hr)).mp hSum

end CalderonN
