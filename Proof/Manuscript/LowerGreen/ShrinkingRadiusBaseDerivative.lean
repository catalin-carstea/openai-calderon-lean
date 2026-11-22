module

public import Proof.CalderonN.Radius
public import Mathlib.Analysis.Calculus.ContDiff.Basic
import Proof.CalderonN.SoftplusProfile
import Mathlib.Tactic

public section

open Set Metric CalderonN
open scoped ContDiff Topology

namespace CalderonPaper.LowerGreen

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- Uniform control of the genuine base derivative of the radius, with
no radius loss, even when the softplus parameter tends to zero. -/
theorem exists_uniform_shrinkingRadius_baseDerivative {Y : Set X} (hY : IsCompact Y)
    {t : X → ℝ} (ht : ContDiff ℝ ∞ t) {R : ℝ} (hR : 0 ≤ R) {p : ℕ} :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ δ ∈ Ioc (0 : ℝ) 1, ∀ y ∈ Y,
      ‖fderiv ℝ (shrinkingRadius R p t δ) y‖ ≤ C := by
  obtain ⟨A,hA⟩ := hY.exists_bound_of_continuousOn ht.continuous.continuousOn
  obtain ⟨D,hD⟩ := hY.exists_bound_of_continuousOn
    (ht.fderiv_right (m := ∞) (by simp)).continuous.continuousOn
  let T := Real.log (1 + Real.exp A)
  have hT : 0 ≤ T := (SoftplusProfile.log_exp_add_one_pos A).le
  let C := R * (p : ℝ) * T^(p-1) * (max 0 D)
  refine ⟨C, by dsimp only [C]; positivity, ?_⟩
  intro δ hδ y hy
  let s := softplus δ
  let B := Real.exp (t y / δ) / (1 + Real.exp (t y / δ))
  have hB₀ : 0 ≤ B := (SoftplusProfile.softplus_derivative_pos δ (t y)).le
  have hB₁ : B ≤ 1 := (SoftplusProfile.softplus_derivative_lt_one δ (t y)).le
  have hs0 : 0 ≤ s (t y) := (softplus_pos hδ.1 _).le
  have hsT : s (t y) ≤ T := SoftplusProfile.softplus_le_log_exp_upper δ (t y) A hδ.1 hδ.2
    ((le_abs_self _).trans (by simpa only [Real.norm_eq_abs] using hA y hy))
  have hs : HasDerivAt s B (t y) := SoftplusProfile.hasDerivAt_softplus δ (t y) hδ.1.ne'
  have hst : HasFDerivAt (s ∘ t) (B • fderiv ℝ t y) y :=
    hs.comp_hasFDerivAt y ((ht.differentiable (by simp) y).hasFDerivAt)
  have hd : HasFDerivAt (shrinkingRadius R p t δ)
      ((R * (p : ℝ) * s (t y)^(p-1) * B) • fderiv ℝ t y) y := by
    change HasFDerivAt (fun x => R * (s ∘ t) x ^ p) _ y
    convert (hst.pow p).const_mul R using 1
    simp only [Function.comp_apply,smul_smul,nsmul_eq_mul,mul_assoc]
  rw [hd.fderiv, norm_smul, Real.norm_of_nonneg (by positivity)]
  have hPow : s (t y)^(p-1) ≤ T^(p-1) := pow_le_pow_left₀ hs0 hsT _
  have hYBound : ‖fderiv ℝ t y‖ ≤ max 0 D := (hD y hy).trans (le_max_right _ _)
  have hCoeff : R * (p : ℝ) * s (t y)^(p-1) * B ≤ R * (p : ℝ) * T^(p-1) := by
    calc
      _ ≤ R * (p : ℝ) * s (t y)^(p-1) * 1 :=
        mul_le_mul_of_nonneg_left hB₁ (by positivity)
      _ ≤ _ := by
        rw [mul_one]
        exact mul_le_mul_of_nonneg_left hPow (by positivity)
  exact mul_le_mul hCoeff hYBound (norm_nonneg _) (by positivity)

end CalderonPaper.LowerGreen
