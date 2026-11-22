module

public import Proof.CalderonN.MetricPair

import Mathlib.LinearAlgebra.Matrix.BilinearForm
import Mathlib.Tactic

public section

open Matrix

namespace CalderonPatch

open CalderonN (I Mat X metricPair metricPair_eq_dotProduct metricPair_pos_of_posDef
  metricPair_smul_metric metricPair_smul_same)

variable {m : ℕ}

private theorem symmetric_eq_of_metric_diagonal {A B : Mat m} (hA : A.IsSymm) (hB : B.IsSymm)
    (h : ∀ v : X m, metricPair (fun _ => A) 0 v v = metricPair (fun _ => B) 0 v v) :
    A = B := by
  let C : (I m → ℝ) →ₗ[ℝ] (I m → ℝ) →ₗ[ℝ] ℝ := Matrix.toLinearMap₂' ℝ A
  let D : (I m → ℝ) →ₗ[ℝ] (I m → ℝ) →ₗ[ℝ] ℝ := Matrix.toLinearMap₂' ℝ B
  have hdiag (v : I m → ℝ) : C v v = D v v := by
    simpa only [C, D, Matrix.toLinearMap₂'_apply', metricPair_eq_dotProduct] using h (WithLp.toLp 2 v)
  have hC (v w : I m → ℝ) : C v w = C w v := by
    simp only [C, Matrix.toLinearMap₂'_apply']
    rw [dotProduct_mulVec, ← mulVec_transpose, hA.eq, dotProduct_comm]
  have hD (v w : I m → ℝ) : D v w = D w v := by
    simp only [D, Matrix.toLinearMap₂'_apply']
    rw [dotProduct_mulVec, ← mulVec_transpose, hB.eq, dotProduct_comm]
  let e : Mat m ≃ₗ[ℝ] (I m → ℝ) →ₗ[ℝ] (I m → ℝ) →ₗ[ℝ] ℝ := Matrix.toLinearMap₂' ℝ
  apply e.injective
  change C = D
  apply LinearMap.ext
  intro v
  apply LinearMap.ext
  intro w
  have hsum := hdiag (v + w)
  simp only [map_add, LinearMap.add_apply] at hsum
  change C v w = D v w
  linarith only [hsum, hdiag v, hdiag w, hC v w, hD v w]

/-- The square of the density-valued principal symbol determines the
tangential metric when the boundary dimension is at least two. -/
theorem boundaryMetric_eq_of_densitySymbolSq_eq (hm : 2 ≤ m)
    {h₁ h₂ : Mat m} (hpos₁ : h₁.PosDef) (hpos₂ : h₂.PosDef)
    (hSymbol : ∀ v : X m,
      h₁.det * metricPair (fun _ => h₁⁻¹) 0 v v =
        h₂.det * metricPair (fun _ => h₂⁻¹) 0 v v) :
    h₁ = h₂ := by
  have hsymm (h : Mat m) (hp : h.PosDef) : (h.det • h⁻¹).IsSymm := by
    unfold Matrix.IsSymm
    rw [transpose_smul, hp.inv.isHermitian.isSymm.eq]
  have hC := symmetric_eq_of_metric_diagonal (hsymm h₁ hpos₁) (hsymm h₂ hpos₂)
    (fun v => by simpa only [metricPair_smul_metric] using hSymbol v)
  have hDet (h : Mat m) (hp : h.PosDef) : (h.det • h⁻¹).det = h.det ^ (m - 1) := by
    rw [Matrix.det_smul, Fintype.card_fin]
    have hpow : h.det ^ m = h.det ^ (m - 1) * h.det := by
      have hm' : m - 1 + 1 = m := by omega
      rw [← pow_succ, hm']
    rw [hpow]
    calc
      _ = h.det ^ (m - 1) * (h⁻¹.det * h.det) := by ring
      _ = _ := by rw [Matrix.det_nonsing_inv_mul_det _ (isUnit_iff_ne_zero.mpr hp.det_pos.ne'), mul_one]
  have hPow : h₁.det ^ (m - 1) = h₂.det ^ (m - 1) :=
    (hDet h₁ hpos₁).symm.trans ((congrArg Matrix.det hC).trans (hDet h₂ hpos₂))
  have hd := (pow_left_inj₀ hpos₁.det_pos.le hpos₂.det_pos.le (by omega : m - 1 ≠ 0)).mp hPow
  have hInv : h₁⁻¹ = h₂⁻¹ := by
    rw [← hd] at hC
    have hc := congrArg (fun M : Mat m => h₁.det⁻¹ • M) hC
    simpa only [smul_smul, inv_mul_cancel₀ hpos₁.det_pos.ne', one_smul] using hc
  calc
    h₁ = h₁ * (h₂⁻¹ * h₂) := by
      rw [Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hpos₂.det_pos.ne'), Matrix.mul_one]
    _ = h₁ * (h₁⁻¹ * h₂) := by rw [hInv]
    _ = h₂ := by
      rw [← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hpos₁.det_pos.ne'),
        Matrix.one_mul]

/-- The top normal derivative is detected by the trace-minus-directional
part of the boundary symbol on the unit sphere of the tangential metric. -/
theorem normalJet_eq_zero_of_trace_direction_eq (hm : 2 ≤ m)
    {h A : Mat m} (hp : h.PosDef) (hA : A.IsSymm)
    (hSymbol : ∀ v : X m, metricPair (fun _ => h) 0 v v = 1 →
      (h⁻¹ * A).trace = metricPair (fun _ => A) 0 v v) :
    A = 0 := by
  let t := (h⁻¹ * A).trace
  have hSymm : (t • h).IsSymm := by
    unfold Matrix.IsSymm
    rw [transpose_smul, hp.isHermitian.isSymm.eq]
  have hscaled : A = t • h := by
    apply symmetric_eq_of_metric_diagonal hA hSymm
    intro v
    rw [metricPair_smul_metric]
    by_cases hv : v = 0
    · simp [hv, metricPair]
    have hPos : 0 < metricPair (fun _ => h) 0 v v := metricPair_pos_of_posDef hp hv
    let r := Real.sqrt (metricPair (fun _ => h) 0 v v)
    have hr : 0 < r := Real.sqrt_pos.2 hPos
    have hSq : r ^ 2 = metricPair (fun _ => h) 0 v v := Real.sq_sqrt hPos.le
    have hu : metricPair (fun _ => h) 0 (r⁻¹ • v) (r⁻¹ • v) = 1 := by
      rw [metricPair_smul_same, inv_pow, ← hSq, inv_mul_cancel₀ (pow_ne_zero 2 hr.ne')]
    have htop := hSymbol (r⁻¹ • v) hu
    rw [metricPair_smul_same] at htop
    change t = (r⁻¹) ^ 2 * metricPair (fun _ => A) 0 v v at htop
    calc
      metricPair (fun _ => A) 0 v v = r ^ 2 * ((r⁻¹) ^ 2 * metricPair (fun _ => A) 0 v v) := by
        rw [← mul_assoc, inv_pow, mul_inv_cancel₀ (pow_ne_zero 2 hr.ne'), one_mul]
      _ = t * metricPair (fun _ => h) 0 v v := by rw [← htop, hSq, mul_comm]
  have ht : t = t * (m : ℝ) := by
    change (h⁻¹ * A).trace = _
    rw [hscaled, Matrix.mul_smul, Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hp.det_pos.ne'),
      Matrix.trace_smul, smul_eq_mul, Matrix.trace_one, Fintype.card_fin]
  have hfactor : t * ((m : ℝ) - 1) = 0 := by linarith
  have hn : (2 : ℝ) ≤ m := by exact_mod_cast hm
  have ht₀ : t = 0 := (mul_eq_zero.mp hfactor).resolve_right (by linarith)
  rw [hscaled, ht₀, zero_smul]

end CalderonPatch
