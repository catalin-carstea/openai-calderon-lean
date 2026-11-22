module

public import Proof.CalderonN.CovariantHessian
public import Proof.CalderonN.Radius
public import Proof.CalderonN.SoftplusProfile

import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

@[expose] public section

noncomputable section
open Set
open scoped BigOperators ContDiff

namespace CalderonN

variable {dim : ℕ}

open SoftplusProfile (logSlope logSlopeDerivative)

theorem contDiff_shrinkingRadius {depth : (X dim) → ℝ} (ht : ContDiff ℝ ∞ depth)
    (R : ℝ) (p : ℕ) (δ : ℝ) :
    ContDiff ℝ ∞ (shrinkingRadius R p depth δ) := by
  unfold shrinkingRadius softplus
  exact contDiff_const.mul ((contDiff_const.mul
    ((contDiff_const.add ((ht.div_const δ).exp)).log (fun _ => by positivity))).pow p)

private theorem log_radius_eq_comp (depth : (X dim) → ℝ) {R δ : ℝ} (hR : 0 < R)
    (hδ : 0 < δ) (p : ℕ) :
    (fun y => Real.log (shrinkingRadius R p depth δ y)) =
      (fun t => Real.log R + (p : ℝ) * Real.log (softplus δ t)) ∘ depth := by
  funext y
  simp only [shrinkingRadius, Function.comp_def,
    Real.log_mul hR.ne' (pow_ne_zero _ (softplus_pos hδ (depth y)).ne'), Real.log_pow]

theorem coordDeriv_log_shrinkingRadius {depth : (X dim) → ℝ} {y : (X dim)}
    (ht : DifferentiableAt ℝ depth y) {R δ : ℝ} (hR : 0 < R) (hδ : 0 < δ) (p : ℕ) (i : (I dim)) :
    coordDeriv i (fun z => Real.log (shrinkingRadius R p depth δ z)) y =
      ((p : ℝ) * logSlope δ (depth y)) * coordDeriv i depth y := by
  rw [log_radius_eq_comp depth hR hδ p]
  exact coordDeriv_scalar_comp ht
    (((SoftplusProfile.hasDerivAt_log_softplus δ (depth y) hδ).const_mul (p : ℝ)).const_add
      (Real.log R)) i

/-- The profile slope and the norm of the fixed depth covector are the
two factors in the exact geometric beta of Proposition 5.3. -/
theorem beta_shrinkingRadius {depth : (X dim) → ℝ} {y : (X dim)}
    (ht : DifferentiableAt ℝ depth y) {R δ : ℝ} (hR : 0 < R) (hδ : 0 < δ)
    (p : ℕ) (γ : (MetricField dim)) :
    beta γ (shrinkingRadius R p depth δ) y =
      (p : ℝ) * logSlope δ (depth y) * Real.sqrt (covectorSq γ depth y) := by
  let a := (p : ℝ) * logSlope δ (depth y)
  have ha : 0 ≤ a := mul_nonneg (Nat.cast_nonneg _) (SoftplusProfile.logSlope_pos δ _ hδ).le
  have hsum :
      (∑ i, ∑ j, (γ y)⁻¹ i j *
        coordDeriv i (fun z => Real.log (shrinkingRadius R p depth δ z)) y *
        coordDeriv j (fun z => Real.log (shrinkingRadius R p depth δ z)) y) =
      a ^ 2 * covectorSq γ depth y := by
    unfold covectorSq
    simp_rw [coordDeriv_log_shrinkingRadius ht hR hδ p, Finset.mul_sum]
    apply Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    dsimp only [a]
    ring
  unfold beta
  dsimp only
  rw [hsum, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq_eq_abs, abs_of_nonneg ha]

theorem metricHessian_log_shrinkingRadius {U : Set (X dim)} (hU : IsOpen U) {depth : (X dim) → ℝ}
    (ht : ContDiffOn ℝ ∞ depth U) {y : (X dim)} (hy : y ∈ U)
    {R δ : ℝ} (hR : 0 < R) (hδ : 0 < δ) (p : ℕ) (γ : (MetricField dim)) (i j : (I dim)) :
    metricHessian γ (fun z => Real.log (shrinkingRadius R p depth δ z)) y i j =
      ((p : ℝ) * logSlope δ (depth y)) * metricHessian γ depth y i j +
      ((p : ℝ) * logSlopeDerivative δ (depth y)) * coordDeriv i depth y * coordDeriv j depth y := by
  rw [log_radius_eq_comp depth hR hδ p]
  exact metricHessian_scalar_comp hU γ ht
    (fun t => ((SoftplusProfile.hasDerivAt_log_softplus δ t hδ).const_mul (p : ℝ)).const_add _)
    hy ((SoftplusProfile.hasDerivAt_logSlope δ (depth y) hδ).const_mul (p : ℝ)) i j

/-- A negative definite depth Hessian gives the strict log-radius
Hessian bound required by the moving-sphere estimate. -/
theorem log_shrinkingRadius_concave {U : Set (X dim)} (hU : IsOpen U) {depth : (X dim) → ℝ}
    (ht : ContDiffOn ℝ ∞ depth U) {y : (X dim)} (hy : y ∈ U)
    {R δ c M : ℝ} (hR : 0 < R) (hδ : 0 < δ) (hc : 0 ≤ c) (hM : 0 < M)
    (p : ℕ) (γ : (MetricField dim)) (hcov : Real.sqrt (covectorSq γ depth y) ≤ M)
    (v : (X dim)) (hmet : 0 ≤ metricPair γ y v v)
    (hess : (∑ i, ∑ j, metricHessian γ depth y i j * v i * v j) ≤ -c * metricPair γ y v v) :
    (∑ i, ∑ j, covJet γ (fun z => Real.log (shrinkingRadius R p depth δ z)) 2 y ![i, j] *
      v i * v j) ≤ -(c / M * beta γ (shrinkingRadius R p depth δ) y) * metricPair γ y v v := by
  let a := (p : ℝ) * logSlope δ (depth y)
  let a' := (p : ℝ) * logSlopeDerivative δ (depth y)
  have ha : 0 ≤ a := mul_nonneg (Nat.cast_nonneg _) (SoftplusProfile.logSlope_pos δ _ hδ).le
  have ha' : a' ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg _)
    (SoftplusProfile.logSlopeDerivative_neg δ _ hδ).le
  have hsum :
      (∑ i, ∑ j, covJet γ (fun z => Real.log (shrinkingRadius R p depth δ z)) 2 y ![i, j] *
        v i * v j) =
      a * (∑ i, ∑ j, metricHessian γ depth y i j * v i * v j) +
        a' * (∑ i, coordDeriv i depth y * v i) ^ 2 := by
    simp_rw [covJet_two_eq_metricHessian, metricHessian_log_shrinkingRadius hU ht hy hR hδ,
      pow_two, Finset.mul_sum, Finset.sum_mul]
    simp_rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    dsimp only [a, a']
    ring
  have hzero : a' * (∑ i, coordDeriv i depth y * v i) ^ 2 ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg ha' (sq_nonneg _)
  have hb : c / M * beta γ (shrinkingRadius R p depth δ) y ≤ c * a := by
    rw [beta_shrinkingRadius ((ht.differentiableOn (by simp)).differentiableAt (hU.mem_nhds hy)) hR hδ]
    change c / M * (a * Real.sqrt (covectorSq γ depth y)) ≤ c * a
    calc
      _ ≤ c / M * (a * M) := mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hcov ha) (div_nonneg hc hM.le)
      _ = c * a := by field_simp
  rw [hsum]
  calc
    _ ≤ a * (-c * metricPair γ y v v) := add_le_of_le_of_nonpos
      (mul_le_mul_of_nonneg_left hess ha) hzero
    _ ≤ _ := by
      rw [show a * (-c * metricPair γ y v v) = -(c * a) * metricPair γ y v v by ring]
      exact mul_le_mul_of_nonneg_right (neg_le_neg hb) hmet

theorem shrinkingRadius_mul_beta_sq_le {depth : (X dim) → ℝ} {y : (X dim)}
    (ht : DifferentiableAt ℝ depth y) {R δ T M : ℝ} (hR : 0 < R) (hδ : 0 < δ) (hδ₁ : δ ≤ 1)
    (hy : depth y ≤ T) (hM : 0 ≤ M) {p : ℕ} (hp : 2 ≤ p) (γ : (MetricField dim))
    (hcov : Real.sqrt (covectorSq γ depth y) ≤ M) :
    shrinkingRadius R p depth δ y * (beta γ (shrinkingRadius R p depth δ) y) ^ 2 ≤
      R * (p : ℝ)^2 * M^2 * (Real.log (1 + Real.exp T))^(p - 2) := by
  apply SoftplusProfile.radius_gradient_uniform_scale_bound δ (depth y) T R M
    (beta γ (shrinkingRadius R p depth δ) y) p hδ hδ₁ hy hR.le hM (Real.sqrt_nonneg _) hp
  rw [beta_shrinkingRadius ht hR hδ, show (p : ℝ) * M * logSlope δ (depth y) =
    ((p : ℝ) * logSlope δ (depth y)) * M by ring]
  exact mul_le_mul_of_nonneg_left hcov
    (mul_nonneg (Nat.cast_nonneg _) (SoftplusProfile.logSlope_pos δ _ hδ).le)

end CalderonN
