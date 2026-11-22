module

public import Proof.CalderonN.Chart

import Mathlib.Analysis.Matrix.Order
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

public section

/- Port of Proof/LocalMetricExtension/NormalizedMetric.lean from the 3D Theorem 3.1
   release (55d37bfe). -/

noncomputable section
open scoped MatrixOrder

namespace CalderonN

variable {n : ℕ} [NeZero n]

/-- Positivity of the normalization denominator. The square-root argument
follows `trace_mul_pos_of_posDef` in the earlier Calderón formalization. -/
theorem trace_mul_pos_of_posDef {A B : Mat n} (hA : A.PosDef) (hB : B.PosDef) :
    0 < (A * B).trace := by
  let S : Mat n := CFC.sqrt A
  have hS : S.PosSemidef := Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg A)
  have hsq : S * S = A := by
    simpa only [S, pow_two] using CFC.sq_sqrt A hA.posSemidef.nonneg
  have hpow : IsUnit (S ^ 2) := by simpa only [pow_two, hsq] using hA.isUnit
  have hunit : IsUnit S := (isUnit_pow_iff (by decide : (2 : ℕ) ≠ 0)).mp hpow
  have ht := (hB.conjTranspose_mul_mul_same (Matrix.mulVec_injective_of_isUnit hunit)).trace_pos
  rw [hS.isHermitian.eq, Matrix.trace_mul_cycle, hsq] at ht
  exact ht

theorem trace_normalized_difference {γ g : MetricField n} {y : X n}
    (hγ : (γ y).PosDef) (hg : (g y).PosDef) :
    (γ y * (principal γ g y - (γ y)⁻¹)).trace = 0 := by
  have htr := trace_mul_pos_of_posDef hγ hg.inv
  rw [Matrix.mul_sub, Matrix.trace_sub, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hγ.det_pos.ne')]
  unfold principal
  rw [Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul, div_mul_cancel₀ _ htr.ne']
  norm_num [Matrix.trace_one, I]

theorem exists_pos_smul_of_principal_eq_inv {γ g : MetricField n} {y : X n}
    (hγ : (γ y).PosDef) (hg : (g y).PosDef)
    (heq : principal γ g y = (γ y)⁻¹) :
    ∃ c : ℝ, 0 < c ∧ g y = c • γ y := by
  let c := (n : ℝ) / (γ y * (g y)⁻¹).trace
  refine ⟨c, div_pos (by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne n)) (trace_mul_pos_of_posDef hγ hg.inv), ?_⟩
  have heq' : c • (g y)⁻¹ = (γ y)⁻¹ := heq
  calc
    g y = γ y * ((γ y)⁻¹ * g y) := by
      rw [← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hγ.det_pos.ne'),
        Matrix.one_mul]
    _ = γ y * ((c • (g y)⁻¹) * g y) := by rw [heq']
    _ = c • γ y := by
      rw [Matrix.smul_mul, Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hg.det_pos.ne'),
        Matrix.mul_smul, Matrix.mul_one]

theorem principal_eq_inv_of_pos_smul {γ g : MetricField n} {y : X n} (hg : (g y).PosDef)
    {c : ℝ} (hc : 0 < c) (hγ : γ y = c • g y) :
    principal γ g y = (γ y)⁻¹ := by
  let u : ℝˣ := Units.mk0 c hc.ne'
  have hInv : (c • g y)⁻¹ = c⁻¹ • (g y)⁻¹ :=
    Matrix.inv_smul' _ u (isUnit_iff_ne_zero.mpr hg.det_pos.ne')
  have htrace : ((c • g y) * (g y)⁻¹).trace = c * (n : ℝ) := by
    rw [Matrix.smul_mul, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hg.det_pos.ne'),
      Matrix.trace_smul, smul_eq_mul]
    norm_num [Matrix.trace_one, I]
  unfold principal
  rw [hγ, hInv, htrace, show (n : ℝ) / (c * (n : ℝ)) = c⁻¹ by
    have hn : (n : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne n
    field_simp [hc.ne', hn]]

end CalderonN
