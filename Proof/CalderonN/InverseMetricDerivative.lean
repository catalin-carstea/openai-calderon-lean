module

public import Proof.CalderonN.InverseMetricBounds
import Proof.CalderonN.MetricVolumeDifferential

import Mathlib.Tactic

@[expose] public section

noncomputable section
set_option autoImplicit false
open Set
open scoped ContDiff
namespace CalderonN
variable {n : ℕ}

/-- The inverse derivative is obtained by differentiating the actual matrix inverse
    identity on the coordinate domain, then multiplying by the same inverse. -/
theorem fderiv_inverse_metric_entries {Ω : Set (X n)} (hΩ : IsOpen Ω) {K : ℝ} {g : (MetricField n)}
    (h : Elliptic Ω K g) (hK : 0 < K) {y : (X n)} (hy : y ∈ Ω) (a : (X n)) (i j : (I n)) :
    fderiv ℝ (fun x => (g x)⁻¹ i j) y a =
      -(∑ k, ∑ l, (g y)⁻¹ i k * fderiv ℝ (fun x => g x k l) y a * (g y)⁻¹ l j) := by
  exact fderiv_inverseMetric_entry_apply g y a
    (fun i j => ((h.1 i j).contDiffAt (hΩ.mem_nhds hy)).differentiableAt (by simp))
    (h.posDef hK hy) i j

/-- A coordinate derivative of the inverse uses only ellipticity and the first derivative
    budget. The estimate is valid in every ambient direction. -/
theorem Elliptic.inverse_derivative_entry_bound {Ω : Set (X n)} (hΩ : IsOpen Ω) {K : ℝ} {g : (MetricField n)}
    (h : Elliptic Ω K g) (hK : 0 < K) {y : (X n)} (hy : y ∈ Ω)
    (M₁ : ℝ) (hM : 0 ≤ M₁) (hD : ∀ i j, ‖fderiv ℝ (fun x => g x i j) y‖ ≤ M₁)
    (a : (X n)) (i j : (I n)) :
    |fderiv ℝ (fun x => (g x)⁻¹ i j) y a| ≤ (n:ℝ)^2*K^2*M₁*‖a‖ := by
  rw [fderiv_inverse_metric_entries hΩ h hK hy, abs_neg]
  have hh (k l : (I n)) : |(g y)⁻¹ i k * fderiv ℝ (fun x => g x k l) y a * (g y)⁻¹ l j| ≤
      K*(M₁*‖a‖)*K := by
    rw [abs_mul,abs_mul]
    exact mul_le_mul (mul_le_mul (h.inverse_entry_bound hK hy i k)
      (((fderiv ℝ (fun x => g x k l) y).le_opNorm a).trans
        (mul_le_mul_of_nonneg_right (hD k l) (norm_nonneg a))) (abs_nonneg _) hK.le)
      (h.inverse_entry_bound hK hy l j) (abs_nonneg _) (by positivity)
  calc
    _ ≤ ∑ k, ∑ l, |(g y)⁻¹ i k * fderiv ℝ (fun x => g x k l) y a * (g y)⁻¹ l j| := by
      exact (Finset.abs_sum_le_sum_abs _ _).trans
        (Finset.sum_le_sum (fun k _ => Finset.abs_sum_le_sum_abs _ _))
    _ ≤ ∑ _k : (I n), ∑ _l : (I n), K*(M₁*‖a‖)*K := Finset.sum_le_sum (fun k _ => Finset.sum_le_sum (fun l _ => hh k l))
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring

end CalderonN
