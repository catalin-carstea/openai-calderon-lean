module

public import Proof.CalderonN.FixedBallGreenPairing
public import Proof.CalderonN.NormalDivergenceScale

import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Tactic

/-! Adapted from `ConstantMetricScale` in the checked Theorem 3.1 release. -/

public section

set_option maxHeartbeats 1600000

noncomputable section
open Set
open scoped ContDiff Matrix InnerProductSpace

namespace CalderonN

variable {dim : ℕ} [NeZero dim]

private theorem metric_inv_const_smul {a : (Mat dim)} {c : ℝ}
    (hc : c ≠ 0) (ha : a.det ≠ 0) : (c • a)⁻¹ = c⁻¹ • a⁻¹ := by
  let u := Units.mk0 c hc
  exact Matrix.inv_smul' _ u (isUnit_iff_ne_zero.mpr ha)

private theorem coordDeriv_const_scaled
    {f : (X dim) → ℝ} {x : (X dim)} (hf : DifferentiableAt ℝ f x) (c : ℝ) (i : (I dim)) :
    coordDeriv i (fun y => c * f y) x = c * coordDeriv i f x := by
  unfold coordDeriv
  rw [fderiv_const_mul hf]
  exact smul_eq_mul _ _

theorem christoffel_const_smul {g : (MetricField dim)} {c : ℝ} (hc : c ≠ 0) {x : (X dim)}
    (hdet : (g x).det ≠ 0) (hg : ∀ i j, DifferentiableAt ℝ (fun y => g y i j) x)
    (k i j : (I dim)) :
    christoffel (c • g) x k i j = christoffel g x k i j := by
  have hInv : ((c • g) x)⁻¹ = c⁻¹ • (g x)⁻¹ := metric_inv_const_smul hc hdet
  have hD (i j k : (I dim)) : coordDeriv k (fun y => (c • g) y i j) x =
      c * coordDeriv k (fun y => g y i j) x :=
    coordDeriv_const_scaled (hg i j) c k
  simp only [christoffel,hInv,Matrix.smul_apply,smul_eq_mul,hD]
  congr 1
  apply Finset.sum_congr rfl
  intro l _
  field_simp

/-- Multiplication of a metric by a constant preserves its harmonic
functions. The Laplacian scales by the reciprocal constant. -/
theorem laplace_const_smul {g : (MetricField dim)} {c : ℝ} (hc : c ≠ 0) {x : (X dim)}
    (hdet : (g x).det ≠ 0) (hg : ∀ i j, DifferentiableAt ℝ (fun y => g y i j) x)
    (u : (X dim) → ℝ) :
    laplace (c • g) u x = c⁻¹ * laplace g u x := by
  have hInv : ((c • g) x)⁻¹ = c⁻¹ • (g x)⁻¹ := metric_inv_const_smul hc hdet
  simp only [laplace,hInv,Matrix.smul_apply,smul_eq_mul,christoffel_const_smul hc hdet hg,Finset.mul_sum,mul_assoc]

theorem ballConormal_scaledMetric_sq (hn : 2 ≤ dim) (g : MetricField dim) (u : X dim → ℝ) (x : X dim)
    (hdet : (g x).det ≠ 0) {r : ℝ} (hr : 0 < r) :
    ballConormal (r^2 • g) u x = r^(dim-2) * ballConormal g u x := by
  have he : metricFluxVector (r^2 • g) u x = r^(dim-2) • metricFluxVector g u x := by
    ext i
    have hscale : r^2 • g = fun y => r^2 • g y := rfl
    simp only [hscale,metricFluxVector,PiLp.toLp_apply,PiLp.smul_apply,smul_eq_mul,
      divergenceFlux,divergenceCoeff_scale_sq hn g r hr x (isUnit_iff_ne_zero.mpr hdet),Finset.mul_sum,mul_assoc]
  rw [ballConormal,he,real_inner_smul_right,ballConormal]

end CalderonN
