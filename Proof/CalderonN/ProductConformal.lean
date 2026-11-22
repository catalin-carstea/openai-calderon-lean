module

public import Proof.CalderonN.ProductMetricHessian

import Proof.CalderonN.Conformal
import Proof.CalderonN.MetricPair
import Proof.CalderonN.SphereFrame
import Proof.CalderonN.ChartBilinear
import Proof.CalderonN.ProductPhaseAlgebra
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Tactic

public section

noncomputable section
open Set Matrix
open scoped ContDiff

namespace CalderonN

variable {dim : ℕ} [NeZero dim]

private theorem metricGradient_smul_metric {g : (MetricField dim)} {x : (X dim)} (hg : (g x).PosDef)
    (c f : (X dim) → ℝ) (hc : 0 < c x) :
    chartMetricGradient (fun y => c y • g y) f x = (c x)⁻¹ • chartMetricGradient g f x := by
  have hinv : (c x • g x)⁻¹ = (c x)⁻¹ • (g x)⁻¹ :=
    Matrix.inv_smul' _ (Units.mk0 (c x) hc.ne') (isUnit_iff_ne_zero.mpr hg.det_pos.ne')
  ext i
  change (∑ j, (c x • g x)⁻¹ i j * coordDeriv j f x) =
    (c x)⁻¹ * ∑ j, (g x)⁻¹ i j * coordDeriv j f x
  rw [hinv, Finset.mul_sum]
  exact Finset.sum_congr rfl fun j _ => by simp only [Matrix.smul_apply, smul_eq_mul, mul_assoc]

private theorem covectorSq_smul_metric {g : (MetricField dim)} {x : (X dim)} (hg : (g x).PosDef)
    (c f : (X dim) → ℝ) (hc : 0 < c x) :
    covectorSq (fun y => c y • g y) f x = (c x)⁻¹ * covectorSq g f x := by
  have hinv : (c x • g x)⁻¹ = (c x)⁻¹ • (g x)⁻¹ :=
    Matrix.inv_smul' _ (Units.mk0 (c x) hc.ne') (isUnit_iff_ne_zero.mpr hg.det_pos.ne')
  unfold covectorSq
  simp only [hinv, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum, mul_assoc]

private theorem normalizedGradient_smul_metric {g : (MetricField dim)} {x : (X dim)} (hg : (g x).PosDef)
    (c f : (X dim) → ℝ) (hc : 0 < c x) :
    (covectorSq (fun y => c y • g y) f x)⁻¹ • chartMetricGradient (fun y => c y • g y) f x =
      (covectorSq g f x)⁻¹ • chartMetricGradient g f x := by
  rw [metricGradient_smul_metric hg c f hc,covectorSq_smul_metric hg c f hc,
    smul_smul, _root_.mul_inv_rev, inv_inv, mul_assoc, mul_inv_cancel₀ hc.ne', mul_one]

private theorem connection_apply_conformal_diagonal
    {g : (MetricField dim)} (hg : SmoothMetric univ g) {c : (X dim) → ℝ}
    (x v : (X dim)) (hc : DifferentiableAt ℝ c x) (hpos : 0 < c x) (d : (X dim) →L[ℝ] ℝ) :
    d (connection (fun y => c y • g y) x v v) =
      d (connection g x v v) +
        (2 * fderiv ℝ c x v * d v - metricPair g x v v * d (chartMetricGradient g c x)) / (2*c x) := by
  let C := fderiv ℝ c x
  let H := chartMetricGradient g c x
  let t := metricPair g x v v
  have hC : C v = ∑ i, coordDeriv i c x * v i := covector_axis_sum C v
  have hΓ := christoffel_of_conformal_smul isOpen_univ hg (mem_univ x) hc hpos
  have hVec : connection (fun y => c y • g y) x v v =
      connection g x v v + (2 * c x)⁻¹ • ((2 * C v) • v - t • H) := by
    ext k
    simp only [connection, PiLp.toLp_apply, PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply,
      smul_eq_mul, hΓ, add_mul, Finset.sum_add_distrib]
    congr 1
    change (∑ i, ∑ j,
      (((if k = j then coordDeriv i c x else 0) + (if k = i then coordDeriv j c x else 0) -
        g x i j * H k) / (2 * c x)) * v i * v j) =
      (2 * c x)⁻¹ * (2 * C v * v k - t * H k)
    have hLeft : (∑ i, ∑ j, (if k = j then coordDeriv i c x else 0) * v i * v j) = C v * v k := by
      rw [hC, Finset.sum_mul]
      simp only [ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
    have hRight : (∑ i, ∑ j, (if k = i then coordDeriv j c x else 0) * v i * v j) = C v * v k := by
      rw [Finset.sum_comm]
      rw [hC, Finset.sum_mul]
      simp only [ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
      refine Finset.sum_congr rfl fun j _ => ?_
      ring
    have hMetric : (∑ i, ∑ j, g x i j * H k * v i * v j) = t * H k := by
      simp only [t, metricPair, Finset.sum_mul]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      ring
    calc
      _ = (2 * c x)⁻¹ *
          ((∑ i, ∑ j, (if k = j then coordDeriv i c x else 0) * v i * v j) +
           (∑ i, ∑ j, (if k = i then coordDeriv j c x else 0) * v i * v j) -
           (∑ i, ∑ j, g x i j * H k * v i * v j)) := by
        simp only [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
        ring
      _ = _ := by rw [hLeft, hRight, hMetric]; ring
  rw [hVec, map_add, map_smul, map_sub, map_smul, map_smul]
  change d (connection g x v v) + (2 * c x)⁻¹ * (2 * C v * d v - t * d H) = _
  ring

private theorem connection_neg_diagonal (g : (MetricField dim)) (x v : (X dim)) :
    connection g x (-v) (-v) = connection g x v v := by
  ext i
  simp [connection, PiLp.neg_apply, mul_neg]

private theorem connection_conformal_cancel
    {g : (MetricField dim)} (hg : SmoothMetric univ g) {c : (X dim) → ℝ}
    (x : (X dim)) (hc : DifferentiableAt ℝ c x) (hpos : 0 < c x)
    (f : (X dim) → ℝ) (d : (X dim) →L[ℝ] ℝ) (hd : ∀ i, d (axis i) = coordDeriv i f x)
    (hf : (fun i => coordDeriv i f x) ≠ 0) (v : (X dim))
    (hv : metricPair g x (chartMetricGradient g f x) v = 0)
    (hn : metricPair g x v v = metricPair g x
      ((covectorSq g f x)⁻¹ • chartMetricGradient g f x) ((covectorSq g f x)⁻¹ • chartMetricGradient g f x)) :
    let a := (covectorSq g f x)⁻¹ • chartMetricGradient g f x
    d (connection (fun y => c y • g y) x a a) + d (connection (fun y => c y • g y) x v v) =
      d (connection g x a a) + d (connection g x v v) := by
  intro a
  let n := covectorSq g f x
  have hp := hg.2 x (mem_univ x)
  have hdp (q : (X dim)) : d q = metricPair g x (chartMetricGradient g f x) q := by
    rw [metricPair_metricGradient _ _ _ _ hp, covector_axis_sum d q]
    simp_rw [hd]
  have ha : d a = 1 := by
    rw [covector_axis_sum d a]
    simp_rw [hd]
    exact normalizedGradient_pair g f x hp hf
  have hzero : d v = 0 := (hdp v).trans hv
  have hN : 0 < n := by
    obtain ⟨i,hi⟩ : ∃ i, coordDeriv i f x ≠ 0 := by
      by_contra! hn
      exact hf (funext hn)
    exact covectorSq_pos hp hi
  have hlen : metricPair g x a a = n⁻¹ := by
    change metricPair g x (n⁻¹ • chartMetricGradient g f x) (n⁻¹ • chartMetricGradient g f x) = _
    rw [metricPair_smul_same, metricPair_gradient_self _ _ _ hp]
    change n⁻¹ ^ 2 * n = n⁻¹
    field_simp
  have hmatch : fderiv ℝ c x a = n⁻¹ * d (chartMetricGradient g c x) := by
    change fderiv ℝ c x (n⁻¹ • chartMetricGradient g f x) = _
    rw [map_smul,smul_eq_mul,hdp,metricPair_comm hp (chartMetricGradient g f x)]
    congr 1
    rw [metricPair_metricGradient _ _ _ _ hp, covector_axis_sum (fderiv ℝ c x)]
    rfl
  rw [connection_apply_conformal_diagonal hg x a hc hpos d, connection_apply_conformal_diagonal hg x v hc hpos d,
    ha,hzero,hn,hlen,hmatch]
  ring

/-- The product Hessian test is invariant under independent positive
conformal scalings in its two factors. -/
theorem productStrictHessianAt_conformal_iff
    {g₁ g₂ : (MetricField dim)} (hg₁ : SmoothMetric univ g₁) (hg₂ : SmoothMetric univ g₂)
    {c₁ c₂ : (X dim) → ℝ} {ρ : (X dim) × (X dim) → ℝ} {p : (X dim) × (X dim)} (hρ : DifferentiableAt ℝ ρ p)
    (hc₁ : DifferentiableAt ℝ c₁ p.1) (hc₂ : DifferentiableAt ℝ c₂ p.2)
    (hp₁ : 0 < c₁ p.1) (hp₂ : 0 < c₂ p.2) :
    ProductStrictHessianAt (fun x => c₁ x • g₁ x) (fun x => c₂ x • g₂ x) ρ p ↔
      ProductStrictHessianAt g₁ g₂ ρ p := by
  let f₁ (x : (X dim)) := ρ (x,p.2)
  let f₂ (y : (X dim)) := ρ (p.1,y)
  let d₁ := (fderiv ℝ ρ p).comp (ContinuousLinearMap.inl ℝ (X dim) (X dim))
  let d₂ := (fderiv ℝ ρ p).comp (ContinuousLinearMap.inr ℝ (X dim) (X dim))
  let a₁ : (X dim) := (covectorSq g₁ f₁ p.1)⁻¹ • chartMetricGradient g₁ f₁ p.1
  let a₂ : (X dim) := (covectorSq g₂ f₂ p.2)⁻¹ • chartMetricGradient g₂ f₂ p.2
  let G₁ := fun x => c₁ x • g₁ x
  let G₂ := fun x => c₂ x • g₂ x
  have hpos₁ := hg₁.2 p.1 (mem_univ _)
  have hpos₂ := hg₂.2 p.2 (mem_univ _)
  have hm₁ (v : (X dim)) :
      metricPair G₁ p.1 (chartMetricGradient G₁ f₁ p.1) v = metricPair g₁ p.1 (chartMetricGradient g₁ f₁ p.1) v := by
    rw [metricGradient_smul_metric hpos₁ c₁ f₁ hp₁,
      metricPair_smul_metric, metricPair_smul_left, ← mul_assoc, mul_inv_cancel₀ hp₁.ne', one_mul]
  have hm₂ (v : (X dim)) :
      metricPair G₂ p.2 (chartMetricGradient G₂ f₂ p.2) v = metricPair g₂ p.2 (chartMetricGradient g₂ f₂ p.2) v := by
    rw [metricGradient_smul_metric hpos₂ c₂ f₂ hp₂,
      metricPair_smul_metric, metricPair_smul_left, ← mul_assoc, mul_inv_cancel₀ hp₂.ne', one_mul]
  have hd₁ (i : (I dim)) : d₁ (axis i) = coordDeriv i f₁ p.1 := (slice_coordDeriv ρ p hρ i).1.symm
  have hd₂ (i : (I dim)) : d₂ (axis i) = coordDeriv i f₂ p.2 := (slice_coordDeriv ρ p hρ i).2.symm
  unfold ProductStrictHessianAt
  dsimp only
  rw [normalizedGradient_smul_metric hpos₁ c₁ _ hp₁, normalizedGradient_smul_metric hpos₂ c₂ _ hp₂]
  change (_ ∧ _ ∧ (∀ v w : (X dim), metricPair G₁ p.1 (chartMetricGradient G₁ f₁ p.1) v = 0 →
    metricPair G₁ p.1 v v = metricPair G₁ p.1 a₁ a₁ →
    metricPair G₂ p.2 (chartMetricGradient G₂ f₂ p.2) w = 0 →
    metricPair G₂ p.2 w w = metricPair G₂ p.2 a₂ a₂ →
    0 < productMetricHessian G₁ G₂ ρ p (a₁,-a₂) (a₁,-a₂) +
      productMetricHessian G₁ G₂ ρ p (v,w) (v,w))) ↔ _
  simp_rw [hm₁,hm₂,show ∀ v w, metricPair G₁ p.1 v w = c₁ p.1 * metricPair g₁ p.1 v w from
    fun v w => metricPair_smul_metric g₁ c₁ p.1 v w,
    show ∀ v w, metricPair G₂ p.2 v w = c₂ p.2 * metricPair g₂ p.2 v w from
    fun v w => metricPair_smul_metric g₂ c₂ p.2 v w,
    mul_right_inj' hp₁.ne', mul_right_inj' hp₂.ne']
  have hsum (hdf₁ : (fun i => coordDeriv i f₁ p.1) ≠ 0)
      (hdf₂ : (fun i => coordDeriv i f₂ p.2) ≠ 0)
      (v w : (X dim)) (hvo : metricPair g₁ p.1 (chartMetricGradient g₁ f₁ p.1) v = 0)
      (hvn : metricPair g₁ p.1 v v = metricPair g₁ p.1 a₁ a₁)
      (hwo : metricPair g₂ p.2 (chartMetricGradient g₂ f₂ p.2) w = 0)
      (hwn : metricPair g₂ p.2 w w = metricPair g₂ p.2 a₂ a₂) :
      productMetricHessian G₁ G₂ ρ p (a₁,-a₂) (a₁,-a₂) + productMetricHessian G₁ G₂ ρ p (v,w) (v,w) =
        productMetricHessian g₁ g₂ ρ p (a₁,-a₂) (a₁,-a₂) + productMetricHessian g₁ g₂ ρ p (v,w) (v,w) := by
    have h₁ := connection_conformal_cancel hg₁ p.1 hc₁ hp₁ f₁ d₁ hd₁ hdf₁ v hvo hvn
    have h₂ := connection_conformal_cancel hg₂ p.2 hc₂ hp₂ f₂ d₂ hd₂ hdf₂ w hwo hwn
    unfold productMetricHessian
    have hsplit (u v : (X dim)) : fderiv ℝ ρ p (u,v) = d₁ u + d₂ v :=
      fderiv_product_split (fderiv ℝ ρ p) (u,v)
    simp only [connection_neg_diagonal, hsplit]
    change _ - (d₁ (connection G₁ p.1 a₁ a₁) + d₂ (connection G₂ p.2 a₂ a₂)) +
      (_ - (d₁ (connection G₁ p.1 v v) + d₂ (connection G₂ p.2 w w))) =
      _ - (d₁ (connection g₁ p.1 a₁ a₁) + d₂ (connection g₂ p.2 a₂ a₂)) +
        (_ - (d₁ (connection g₁ p.1 v v) + d₂ (connection g₂ p.2 w w)))
    linarith only [h₁,h₂]
  constructor
  · rintro ⟨h₁,h₂,h⟩
    exact ⟨h₁,h₂,fun v w hvo hvn hwo hwn =>
      (hsum h₁ h₂ v w hvo hvn hwo hwn) ▸ h v w hvo hvn hwo hwn⟩
  · rintro ⟨h₁,h₂,h⟩
    exact ⟨h₁,h₂,fun v w hvo hvn hwo hwn =>
      (hsum h₁ h₂ v w hvo hvn hwo hwn).symm ▸ h v w hvo hvn hwo hwn⟩

end CalderonN
