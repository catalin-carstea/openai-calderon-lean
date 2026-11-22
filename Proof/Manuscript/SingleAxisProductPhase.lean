module

public import Proof.CalderonN.LocalProductPhaseGap

import Proof.CalderonN.MetricPair
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Tactic

public section

noncomputable section
open Set Metric Matrix CalderonN
open scoped ContDiff

namespace CalderonPaper.ScalarElliptic

open ProductHessianSeparation

/-- In one dimension a nonzero covector has no nonzero orthogonal
coordinate, so the prescribed tangential sphere is empty. -/
private theorem single_axis_strictSphereCone (g : MetricField 1) (f : X 1 → ℝ) (x : X 1)
    (hg : (g x).PosDef) (hd : (fun i => coordDeriv i f x) ≠ 0) (P : selfAdjoint (Mat 1)) :
    let a := (covectorSq g f x)⁻¹ • chartMetricGradient g f x
    P ∈ strictSphereCone (g x) (fun i => coordDeriv i f x) (fun i => a i) := by
  intro a v hv
  have hn : coordDeriv (0 : I 1) f x ≠ 0 := fun h => hd (funext fun i => by
    rw [Subsingleton.elim i 0]; exact h)
  have hv₀ : coordDeriv (0 : I 1) f x * v 0 = 0 := by
    simpa only [dotProduct,Fin.sum_univ_one] using hv.1
  have hvz : v = 0 := funext fun i => by
    rw [Subsingleton.elim i 0]
    exact (mul_eq_zero.mp hv₀).resolve_left hn
  have ha : a ≠ 0 := by
    intro h
    have hp := normalizedGradient_pair g f x hg hd
    change (fun i => coordDeriv i f x) ⬝ᵥ (fun i => a i) = 1 at hp
    simp [h] at hp
  have hAp := metricPair_pos_of_posDef hg (v := a) ha
  have hc := hv.2
  simp only [hvz,Matrix.mulVec_zero,zero_dotProduct,← metricPair_eq_dotProduct] at hc
  linarith

private theorem chartBilinear_neg_one (C : ℝ) (v : X 1) :
    chartBilinear ((-C) • (1 : Mat 1)) v v = (-C) * ‖v‖^2 := by
  rw [chartBilinear_apply,EuclideanSpace.real_norm_sq_eq]
  simp only [Matrix.mulVec,dotProduct,Fin.sum_univ_one,Matrix.smul_apply,smul_eq_mul,Matrix.one_apply,
    ite_true,mul_one]
  ring

set_option maxHeartbeats 2500000 in
/-- In the single-axis case the quadratic penalty can be selected
directly. Both strict cone conditions are vacuous. -/
theorem exists_single_axis_blockHessians {g₁ g₂ : MetricField 1}
    (hg₁ : SmoothMetric univ g₁) (hg₂ : SmoothMetric univ g₂)
    {ρ : X 1 × X 1 → ℝ} {z : X 1 × X 1}
    (hstrict : ProductStrictHessianAt g₁ g₂ ρ z) :
    let f₁ : X 1 → ℝ := fun x => ρ (x,z.2)
    let f₂ : X 1 → ℝ := fun y => ρ (z.1,y)
    let a₁ : X 1 := (covectorSq g₁ f₁ z.1)⁻¹ • chartMetricGradient g₁ f₁ z.1
    let a₂ : X 1 := (covectorSq g₂ f₂ z.2)⁻¹ • chartMetricGradient g₂ f₂ z.2
    ∃ (P₁ P₂ : selfAdjoint (Mat 1)) (K : ℝ), 0 < K ∧
      P₁ ∈ strictSphereCone (g₁ z.1) (fun i => coordDeriv i f₁ z.1) (fun i => a₁ i) ∧
      P₂ ∈ strictSphereCone (g₂ z.2) (fun i => coordDeriv i f₂ z.2) (fun i => a₂ i) ∧
      ∀ v : X 1 × X 1, v ≠ 0 → 0 <
        productMetricHessian g₁ g₂ ρ z v v + K * (fderiv ℝ ρ z v)^2 -
          chartBilinear (P₁ : Mat 1) v.1 v.1 - chartBilinear (P₂ : Mat 1) v.2 v.2 := by
  intro f₁ f₂ a₁ a₂
  let E := X 1 × X 1
  let d₁ : X 1 →L[ℝ] ℝ := (fderiv ℝ ρ z).comp (ContinuousLinearMap.inl ℝ (X 1) (X 1))
  let d₂ : X 1 →L[ℝ] ℝ := (fderiv ℝ ρ z).comp (ContinuousLinearMap.inr ℝ (X 1) (X 1))
  let C₁ := chartBilinear (fun i j => ∑ k, d₁ (axis k) * christoffel g₁ z.1 k i j)
  let C₂ := chartBilinear (fun i j => ∑ k, d₂ (axis k) * christoffel g₂ z.2 k i j)
  let Q : E →L[ℝ] E →L[ℝ] ℝ := fderiv ℝ (fderiv ℝ ρ) z
  have hH (v : E) : Q v v - C₁ v.1 v.1 - C₂ v.2 v.2 = productMetricHessian g₁ g₂ ρ z v v := by
    unfold productMetricHessian
    rw [fderiv_product_split (fderiv ℝ ρ z)]
    have h₁ := covector_connection_eq_bilinear g₁ z.1 v.1 v.1 d₁
    have h₂ := covector_connection_eq_bilinear g₂ z.2 v.2 v.2 d₂
    change fderiv ℝ ρ z (connection g₁ z.1 v.1 v.1,0) = C₁ v.1 v.1 at h₁
    change fderiv ℝ ρ z (0,connection g₂ z.2 v.2 v.2) = C₂ v.2 v.2 at h₂
    rw [h₁,h₂]
    ring
  have hCont : Continuous (fun v : E => productMetricHessian g₁ g₂ ρ z v v) := by
    simp_rw [← hH]
    exact (Q.continuous.clm_apply continuous_id).sub
      ((C₁.continuous.comp continuous_fst).clm_apply continuous_fst) |>.sub
        ((C₂.continuous.comp continuous_snd).clm_apply continuous_snd)
  obtain ⟨A,hA⟩ := (isCompact_sphere (0 : E) 1).exists_bound_of_continuousOn hCont.continuousOn
  let C := max A 0 + 1
  have hC : 0 < C := zero_lt_one.trans_le (le_add_of_nonneg_left (le_max_right _ _))
  let P : selfAdjoint (Mat 1) := ⟨(-C) • (1 : Mat 1),by
    change star ((-C) • (1 : Mat 1)) = _
    simp⟩
  refine ⟨P,P,1,one_pos,single_axis_strictSphereCone g₁ f₁ z.1 (hg₁.2 _ (mem_univ _)) hstrict.1 P,
    single_axis_strictSphereCone g₂ f₂ z.2 (hg₂.2 _ (mem_univ _)) hstrict.2.1 P,?_⟩
  intro v hv
  have hn : 0 < ‖v‖ := norm_pos_iff.mpr hv
  let u := ‖v‖⁻¹ • v
  have hu : u ∈ sphere (0 : E) 1 := by
    rw [mem_sphere_zero_iff_norm]
    change ‖‖v‖⁻¹ • v‖ = 1
    rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg (inv_nonneg.mpr hn.le),inv_mul_cancel₀ hn.ne']
  have he : v = ‖v‖ • u := by unfold u; rw [smul_smul,mul_inv_cancel₀ hn.ne',one_smul]
  have hlow : -(max A 0) ≤ productMetricHessian g₁ g₂ ρ z u u :=
    (abs_le.mp ((by simpa only [Real.norm_eq_abs] using hA u hu :
      |productMetricHessian g₁ g₂ ρ z u u| ≤ A).trans (le_max_left _ _))).1
  have hscaled : ‖v‖^2 * (-max A 0) ≤ productMetricHessian g₁ g₂ ρ z v v := by
    have hhom : productMetricHessian g₁ g₂ ρ z v v = ‖v‖^2 * productMetricHessian g₁ g₂ ρ z u u := by
      conv_lhs => rw [he]
      exact productMetricHessian_smul_self g₁ g₂ ρ z u ‖v‖
    rw [hhom]
    exact mul_le_mul_of_nonneg_left hlow (sq_nonneg _)
  have hsum : ‖v‖^2 ≤ ‖v.1‖^2 + ‖v.2‖^2 := by
    rw [Prod.norm_def]
    rcases le_total ‖v.1‖ ‖v.2‖ with h | h
    · rw [max_eq_right h]; exact le_add_of_nonneg_left (sq_nonneg _)
    · rw [max_eq_left h]; exact le_add_of_nonneg_right (sq_nonneg _)
  have hscaledC := mul_le_mul_of_nonneg_left hsum hC.le
  change 0 < _ + 1 * _ -
    chartBilinear ((-C) • (1 : Mat 1)) v.1 v.1 - chartBilinear ((-C) • (1 : Mat 1)) v.2 v.2
  rw [chartBilinear_neg_one,chartBilinear_neg_one]
  have hsq : 0 < ‖v‖^2 := sq_pos_of_pos hn
  dsimp [C] at *
  nlinarith only [hscaled,hscaledC,hsq,sq_nonneg (fderiv ℝ ρ z v)]

end CalderonPaper.ScalarElliptic
