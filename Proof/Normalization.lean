import Proof.MetricAlgebra
import Mathlib.Analysis.Matrix.Order
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith

noncomputable section
open Set
open scoped MatrixOrder Matrix.Norms.L2Operator
namespace ShrinkingSpheres

/-- The matrix argument from the supplied NormalizedPrincipalMetric module. -/
lemma trace_mul_pos (A B : Mat) (hA : A.PosDef) (hB : B.PosDef) :
    0 < (A * B).trace := by
  let S : Mat := CFC.sqrt A
  have hS : S.PosSemidef := Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg A)
  have hsq : S*S=A := by
    simpa only [S,pow_two] using CFC.sq_sqrt A hA.posSemidef.nonneg
  have hpow : IsUnit (S^2) := by simpa only [pow_two,hsq] using hA.isUnit
  have hunit : IsUnit S := (isUnit_pow_iff (by decide : (2 : ℕ) ≠ 0)).mp hpow
  have ht := (hB.conjTranspose_mul_mul_same (Matrix.mulVec_injective_of_isUnit hunit)).trace_pos
  rw [hS.isHermitian.eq,Matrix.trace_mul_cycle,hsq] at ht
  exact ht

lemma Elliptic.posDef {Ω : Set X} {K : ℝ} {g : MetricField}
    (h : Elliptic Ω K g) (hK : 0 < K) {y : X} (hy : y ∈ Ω) : (g y).PosDef := by
  refine Matrix.PosDef.of_dotProduct_mulVec_pos ?_ ?_
  · exact Matrix.isHermitian_iff_isSymm.mpr (h.2 y hy).1
  · intro v hv
    let w : X := WithLp.toLp 2 v
    have hw : w ≠ 0 := by
      intro hzero
      apply hv
      exact congrArg WithLp.ofLp hzero
    have hp : 0 < K⁻¹ * ‖w‖^2 := mul_pos (inv_pos.mpr hK) (sq_pos_of_ne_zero (norm_ne_zero_iff.mpr hw))
    have ht := hp.trans_le ((h.2 y hy).2 w).1
    simpa only [metricPair, w, Matrix.mulVec, dotProduct, Finset.mul_sum, star_trivial, mul_assoc, mul_left_comm] using ht

lemma principal_denominator_pos (γ g₂ : MetricField) (y : X)
    (hγ : (γ y).PosDef) (h₂ : (g₂ y).PosDef) :
    0 < ((γ y) * (g₂ y)⁻¹).trace := trace_mul_pos _ _ hγ h₂.inv

lemma principal_posDef (γ g₂ : MetricField) (y : X)
    (hγ : (γ y).PosDef) (h₂ : (g₂ y).PosDef) : (principal γ g₂ y).PosDef := by
  exact h₂.inv.smul (div_pos (by norm_num) (principal_denominator_pos _ _ _ hγ h₂))

lemma trace_principal (γ g₂ : MetricField) (y : X)
    (hγ : (γ y).PosDef) (h₂ : (g₂ y).PosDef) : ((γ y) * principal γ g₂ y).trace = 3 := by
  rw [principal, Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul]
  exact div_mul_cancel₀ _ (principal_denominator_pos _ _ _ hγ h₂).ne'

lemma trace_principal_difference (γ g₂ : MetricField) (y : X)
    (hγ : (γ y).PosDef) (h₂ : (g₂ y).PosDef) :
    ((γ y) * (principal γ g₂ y - (γ y)⁻¹)).trace = 0 := by
  rw [Matrix.mul_sub, Matrix.trace_sub, trace_principal _ _ _ hγ h₂,
    Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hγ.det_pos.ne'), Matrix.trace_one]
  norm_num

lemma Admissible.principal_properties {Y Ω : Set X} {m : ℕ} {K ρ c₀ floor ε : ℝ}
    {M : Fin (m+1) → ℝ} {Cj : Fin 9 → ℝ} {d : Data}
    (h : Admissible Y Ω K ρ c₀ M Cj floor ε d) (hK : 0 < K) {y : X} (hy : y ∈ Ω) :
    (principal d.γ d.g₂ y).PosDef ∧
      ((d.γ y) * (principal d.γ d.g₂ y - (d.γ y)⁻¹)).trace = 0 := by
  have hγ := h.1.1.posDef hK hy
  have h₂ := h.1.2.2.1.posDef hK hy
  exact ⟨principal_posDef _ _ _ hγ h₂, trace_principal_difference _ _ _ hγ h₂⟩

/-- The reference-connection drift gives precisely the normalized second metric equation. -/
lemma normalized_laplace (γ g₂ : MetricField) (u : X → ℝ) (y : X) :
    (∑ i, ∑ j, principal γ g₂ y i j * (coordDeriv i (coordDeriv j u) y -
      ∑ k, christoffel γ y k i j * coordDeriv k u y)) +
      (∑ k, drift γ g₂ y k * coordDeriv k u y) =
    (3/((γ y)*(g₂ y)⁻¹).trace) * laplace g₂ u y := by
  simp only [principal, drift, laplace, Matrix.smul_apply, smul_eq_mul, Fin.sum_univ_three]
  ring

end ShrinkingSpheres
