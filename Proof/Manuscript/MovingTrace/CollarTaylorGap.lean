module

public import Proof.Manuscript.MovingTrace.SplitOperatorLayerCoefficients
public import Proof.Manuscript.MovingTrace.CollarResidualEnvelopes
public import Mathlib.Tactic
public import Mathlib.Analysis.Calculus.ContDiff.Operations

@[expose] public section

noncomputable section

open CalderonN Set Finset Filter
open scoped ContDiff

namespace CalderonPatch.BoundaryLayer

variable {n : ℕ}
variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] [ProperSpace P]

/-- Collar Taylor polynomials differ from the actual operator coefficient
by a smooth amplitude times one higher normal power, also at zero depth. -/
theorem collarTaylorCoefficient_exact_gap
    {O : Set ((P × X n) × ℝ)} (hO : IsOpen O)
    {a : (P × X n) × ℝ → ℝ} (ha : ContDiffOn ℝ ∞ a O) (M : ℕ) :
    let U := {q : (P × X n) × ℝ | ∀ s ∈ Icc (0 : ℝ) 1, (q.1,s*q.2) ∈ O}
    IsOpen U ∧ ∃ R : (P × X n) × ℝ → ℂ, ContDiffOn ℝ ∞ R U ∧
      ∀ q ∈ U, (a q : ℂ) - (∑ k ∈ range (M+1),
        (q.2 : ℂ)^k * collarTaylorCoefficient a k q.1) = (q.2 : ℂ)^(M+1) * R q := by
  let U := {q : (P × X n) × ℝ | ∀ s ∈ Icc (0 : ℝ) 1, (q.1,s*q.2) ∈ O}
  obtain ⟨hU,R,hR,hEq⟩ := CalderonPaper.normalTaylor_has_smooth_remainder hO ha M
  change IsOpen U ∧ _
  refine ⟨hU, (fun q => (R q : ℂ)), Complex.ofRealCLM.contDiff.comp_contDiffOn hR, ?_⟩
  intro q hq
  apply sub_eq_iff_eq_add.mpr
  have h := congrArg (fun x : ℝ => (x : ℂ)) (hEq q hq)
  simpa only [smul_eq_mul, Complex.ofReal_add, Complex.ofReal_mul,Complex.ofReal_sum,
    Complex.ofReal_pow,Complex.ofReal_div,Complex.ofReal_natCast,collarTaylorCoefficient,div_mul_eq_mul_div,
    mul_div_assoc,add_comm] using h

theorem scalarCoefficientDifference_scale_all
    (A : Matrix (I n) (I n) ℂ) (τ : ℂ) (c : I n → ℂ)
    (ξ : I n → ℝ) (h : ℝ) (V : X n × ℝ → ℂ) (y : X n) (s : ℝ) (z : ℂ) :
    scalarCoefficientDifference (z • A) (z*τ) (z • c) ξ h V y s =
      z * scalarCoefficientDifference A τ c ξ h V y s := by
  unfold scalarCoefficientDifference
  simp only [Matrix.smul_apply,Pi.smul_apply,smul_eq_mul]
  have hSumA (f : I n → I n → ℂ) :
      (∑ i, ∑ j, (z * A i j) * f i j) = z * (∑ i, ∑ j, A i j * f i j) := by
    simp only [Finset.mul_sum]
    apply sum_congr rfl
    intro i _
    apply sum_congr rfl
    intro j _
    ring
  have hSumC (f : I n → ℂ) : (∑ i, (z * c i) * f i) = z * (∑ i, c i * f i) := by
    rw [Finset.mul_sum]
    apply sum_congr rfl
    intro i _
    ring
  have hPrincipal : (∑ i, ∑ j, (z * A i j) * (ξ i : ℂ) * (ξ j : ℂ)) =
      z * (∑ i, ∑ j, A i j * (ξ i : ℂ) * (ξ j : ℂ)) := by
    simpa only [mul_assoc] using hSumA (fun i j => (ξ i : ℂ) * (ξ j : ℂ))
  have hCross : (∑ i, ∑ j, (z * A i j) * (ξ i : ℂ) * splitFirst V y s j) =
      z * (∑ i, ∑ j, A i j * (ξ i : ℂ) * splitFirst V y s j) := by
    simpa only [mul_assoc] using hSumA (fun i j => (ξ i : ℂ) * splitFirst V y s j)
  have hDrift : (∑ i, (z * c i) * (ξ i : ℂ) * V (y,s)) =
      z * (∑ i, c i * (ξ i : ℂ) * V (y,s)) := by
    simpa only [mul_assoc] using hSumC (fun i => (ξ i : ℂ) * V (y,s))
  rw [hPrincipal,hCross,hDrift,hSumA (splitSecond V y s),hSumC (splitFirst V y s)]
  ring

end CalderonPatch.BoundaryLayer
