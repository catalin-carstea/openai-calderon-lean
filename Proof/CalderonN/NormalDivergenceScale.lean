module

public import Proof.CalderonN.MetricDivergence

import Mathlib.Tactic

@[expose] public section

noncomputable section

namespace CalderonN

variable {n : ℕ}

/-- Scaling a metric by a squared radius scales its volume by the nth power. -/
theorem chartVolume_scale_sq (g : MetricField n) (r : ℝ) (hr : 0 < r) (x : X n) :
    chartVolume (fun y => r^2 • g y) x = r^n * chartVolume g x := by
  unfold chartVolume
  rw [Matrix.det_smul, Fintype.card_fin]
  have hPow : (r^2)^n = (r^n)^2 := by rw [← pow_mul, ← pow_mul, mul_comm]
  rw [hPow, Real.sqrt_mul (sq_nonneg (r^n)), Real.sqrt_sq_eq_abs, abs_of_pos (pow_pos hr n)]

/-- The density times the inverse metric scales by the (n−2)nd power.
    This is the divergence coefficient on a radius-scaled normal chart. -/
theorem divergenceCoeff_scale_sq (hn : 2 ≤ n) (g : MetricField n) (r : ℝ)
    (hr : 0 < r) (x : X n) (hDet : IsUnit (g x).det) (i j : I n) :
    divergenceCoeff (fun y => r^2 • g y) x i j = r^(n-2) * divergenceCoeff g x i j := by
  let u : ℝˣ := Units.mk0 (r^2) (pow_ne_zero 2 hr.ne')
  have hInv : (r^2 • g x)⁻¹ = (r^2)⁻¹ • (g x)⁻¹ :=
    Matrix.inv_smul' (g x) u hDet
  rw [divergenceCoeff, chartVolume_scale_sq g r hr, hInv, Matrix.smul_apply, smul_eq_mul,
    divergenceCoeff]
  have hp : r^n = r^(n-2) * r^2 := by rw [← pow_add, Nat.sub_add_cancel hn]
  rw [hp]
  field_simp [hr.ne']

end CalderonN
