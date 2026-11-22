module

public import Proof.CalderonN.ProductPhaseAlgebra
public import Proof.CalderonN.SphereFrame

import Proof.CalderonN.ChartBilinear
import Proof.CalderonN.ChartGeometry
import Proof.CalderonN.MetricPair
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic

@[expose] public section

noncomputable section
open Set Matrix Filter
open scoped ContDiff Topology InnerProductSpace

namespace CalderonN

variable {dim : ℕ} [NeZero dim]

private theorem fderiv_radius_eq_smul_log {r : (X dim) → ℝ} {y : (X dim)}
    (hr : DifferentiableAt ℝ r y) (hy : 0 < r y) :
    fderiv ℝ r y = r y • fderiv ℝ (fun x => Real.log (r x)) y := by
  rw [(hr.hasFDerivAt.log hy.ne').fderiv, smul_smul, mul_inv_cancel₀ hy.ne', one_smul]

/-- The differentiated radius term in the Hessian uses the same logarithmic
profile as the coercivity estimate. -/
theorem radius_covariantHessian_eq_log
    {Y : Set (X dim)} (hY : IsOpen Y) (g : (MetricField dim)) {r : (X dim) → ℝ}
    (hr : ContDiffOn ℝ ∞ r Y) (hpos : ∀ y ∈ Y, 0 < r y)
    {y : (X dim)} (hy : y ∈ Y) (u : (X dim)) :
    fderiv ℝ r y u ^ 2 + r y * metricHessianEval g r y u u =
      2 * fderiv ℝ r y u ^ 2 +
        (r y)^2 * metricHessianEval g (fun z => Real.log (r z)) y u u := by
  let f (z : (X dim)) := Real.log (r z)
  have hf : ContDiffOn ℝ ∞ f Y := hr.log fun z hz => (hpos z hz).ne'
  have heq : EqOn r (Real.exp ∘ f) Y := fun z hz => (Real.exp_log (hpos z hz)).symm
  have hD (i : (I dim)) := eqOn_coordDeriv hY heq i
  have hH (i j : (I dim)) : metricHessian g r y i j =
      r y * metricHessian g f y i j + r y * coordDeriv i f y * coordDeriv j f y := by
    have he : metricHessian g r y i j = metricHessian g (Real.exp ∘ f) y i j := by
      simp only [metricHessian,hessian,eqOn_coordDeriv hY (hD j) i hy,fun k => hD k hy]
    rw [he,metricHessian_scalar_comp hY g hf Real.hasDerivAt_exp hy
      (Real.hasDerivAt_exp (f y)), show Real.exp (f y) = r y from (heq hy).symm]
  have hsum : fderiv ℝ f y u = ∑ i, coordDeriv i f y * u i :=
    covector_axis_sum (fderiv ℝ f y) u
  have hdf := fderiv_radius_eq_smul_log
    ((hr.contDiffAt (hY.mem_nhds hy)).differentiableAt (by simp)) (hpos y hy)
  rw [hdf,_root_.smul_apply,smul_eq_mul]
  change (r y * fderiv ℝ f y u)^2 + r y * metricHessianEval g r y u u =
    2 * (r y * fderiv ℝ f y u)^2 + (r y)^2 * metricHessianEval g f y u u
  simp only [metricHessianEval, hH, hsum]
  have hExpand :
      (∑ i, ∑ j, (r y * metricHessian g f y i j +
        r y * coordDeriv i f y * coordDeriv j f y) * u i * u j) =
      r y * (∑ i, ∑ j, metricHessian g f y i j * u i * u j) +
      r y * (∑ i, coordDeriv i f y * u i)^2 := by
    rw [pow_two]
    simp only [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  rw [hExpand]
  ring

theorem radius_covariantHessian_le_of_profile
    {Y : Set (X dim)} (hY : IsOpen Y) {g : (MetricField dim)} {r : (X dim) → ℝ}
    {e : (Frame dim)} {floor c₀ : ℝ} {Cj : Fin 9 → ℝ} (hprof : Profile Y g e r floor c₀ Cj)
    {y : (X dim)} (hy : y ∈ Y) (u : (X dim)) :
    fderiv ℝ r y u ^ 2 + r y * metricHessianEval g r y u u ≤
      2 * fderiv ℝ r y u ^ 2 - (c₀ * beta g r y * (r y)^2) * metricPair g y u u := by
  rw [radius_covariantHessian_eq_log hY g hprof.1 (fun z hz => (hprof.2 z hz).1) hy u]
  have h := (hprof.2 y hy).2.2.1 u
  simp only [covJet_two_eq_metricHessian] at h
  change metricHessianEval g (fun z => Real.log (r z)) y u u ≤ _ at h
  have hm := mul_le_mul_of_nonneg_left h (sq_nonneg (r y))
  linarith only [hm]

theorem fderiv_eq_inner_frameCoordinates_chartMetricGradient (g : (MetricField dim)) (y u : (X dim))
    (hpos : (g y).PosDef) (e : (I dim) → (X dim))
    (he : ∀ i j, metricPair g y (e i) (e j) = if i = j then 1 else 0) (f : (X dim) → ℝ) :
    fderiv ℝ f y u =
      ⟪frameCoordinates g y e (chartMetricGradient g f y),frameCoordinates g y e u⟫_ℝ := by
  rw [inner_frameCoordinates g y _ u e he,metricPair_metricGradient _ _ _ _ hpos]
  exact covector_axis_sum (fderiv ℝ f y) u

theorem norm_framed_radiusGradient_eq
    {g : (MetricField dim)} {y : (X dim)} (hpos : (g y).PosDef) (e : (I dim) → (X dim))
    (he : ∀ i j, metricPair g y (e i) (e j) = if i = j then 1 else 0)
    {r : (X dim) → ℝ} (hr : DifferentiableAt ℝ r y) (hy : 0 < r y) :
    ‖frameCoordinates g y e (chartMetricGradient g r y)‖ = r y * beta g r y := by
  let f (z : (X dim)) := Real.log (r z)
  have hcol (i : (I dim)) : coordDeriv i r y = r y * coordDeriv i f y := by
    unfold coordDeriv f
    rw [fderiv_radius_eq_smul_log hr hy,_root_.smul_apply,smul_eq_mul]
  have hsq : covectorSq g r y = (r y)^2 * covectorSq g f y := by
    simp only [covectorSq, hcol, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  have hf : 0 ≤ covectorSq g f y := by
    rw [← metricPair_gradient_self g f y hpos]
    exact metricPair_nonneg_of_posDef hpos _
  have hβ : beta g r y = Real.sqrt (covectorSq g f y) := rfl
  apply (sq_eq_sq₀ (norm_nonneg _) (by rw [hβ]; positivity)).mp
  rw [norm_frameCoordinates_sq g y _ e he,metricPair_gradient_self g r y hpos,
    hsq,hβ,mul_pow,Real.sq_sqrt hf]

end CalderonN
