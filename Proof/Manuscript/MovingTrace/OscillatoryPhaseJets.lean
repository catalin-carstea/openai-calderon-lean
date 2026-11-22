module

public import Proof.Manuscript.MovingTrace.ExponentialProfileJets
public import Mathlib.Tactic
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Calculus.ContDiff.Bounds
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

@[expose] public section

noncomputable section

open CalderonN Set
open scoped ContDiff

namespace CalderonPaper

private def unitPhase (x : ℝ) : ℂ := Complex.exp (Complex.I * (x : ℂ))

def imaginaryInclusion : ℝ →L[ℝ] ℂ :=
  (ContinuousLinearMap.mul ℝ ℂ Complex.I).comp Complex.ofRealCLM

def oscillatoryPhaseJetBound : ℝ := ‖Complex.ofRealCLM‖ + ‖imaginaryInclusion‖

theorem oscillatoryPhaseJetBound_nonneg : 0 ≤ oscillatoryPhaseJetBound := by
  unfold oscillatoryPhaseJetBound
  positivity

private theorem unitPhase_eq :
    unitPhase = fun x => (Complex.ofRealCLM ∘ Real.cos) x + (imaginaryInclusion ∘ Real.sin) x := by
  funext x
  rw [unitPhase,mul_comm Complex.I,Complex.exp_mul_I]
  simp [imaginaryInclusion]
  ring

private theorem unitPhase_contDiff : ContDiff ℝ ∞ unitPhase := by
  rw [unitPhase_eq]
  exact (Complex.ofRealCLM.contDiff.comp Real.contDiff_cos).add
    (imaginaryInclusion.contDiff.comp Real.contDiff_sin)

private theorem unitPhase_iteratedFDeriv_norm (j : ℕ) (x : ℝ) :
    ‖iteratedFDeriv ℝ j unitPhase x‖ ≤ oscillatoryPhaseJetBound := by
  let L := Complex.ofRealCLM
  let M := imaginaryInclusion
  have hcos : ContDiffAt ℝ j (L ∘ Real.cos) x := (L.contDiff.comp Real.contDiff_cos).contDiffAt
  have hsin : ContDiffAt ℝ j (M ∘ Real.sin) x := (M.contDiff.comp Real.contDiff_sin).contDiffAt
  rw [unitPhase_eq,fun_iteratedFDeriv_add_apply hcos hsin]
  refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
  · refine (L.norm_iteratedFDeriv_comp_left Real.contDiff_cos.contDiffAt (le_refl _)).trans ?_
    have h := mul_le_mul_of_nonneg_left (Real.abs_iteratedDeriv_cos_le_one j x) (norm_nonneg L)
    simpa only [norm_iteratedFDeriv_eq_norm_iteratedDeriv,Real.norm_eq_abs,mul_one] using h
  · refine (M.norm_iteratedFDeriv_comp_left Real.contDiff_sin.contDiffAt (le_refl _)).trans ?_
    have h := mul_le_mul_of_nonneg_left (Real.abs_iteratedDeriv_sin_le_one j x) (norm_nonneg M)
    simpa only [norm_iteratedFDeriv_eq_norm_iteratedDeriv,Real.norm_eq_abs,mul_one] using h

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Uniform phase control with the semiclassical scale frozen during
differentiation. The modulus of the plane wave is one. -/
theorem norm_iteratedFDeriv_oscillatoryPhase_le
    {phase : E → ℝ} {q : E} (hp : ContDiffAt ℝ ∞ phase q)
    {A : ℝ} (hA : 1 ≤ A) (N : ℕ)
    (hJet : ∀ i, 1 ≤ i → i ≤ N → ‖iteratedFDeriv ℝ i phase q‖ ≤ A)
    {h : ℝ} (hh : 0 < h) (hh₁ : h ≤ 1) (j : ℕ) (hj : j ≤ N) :
    ‖iteratedFDeriv ℝ j (fun y => Complex.exp (Complex.I * (phase y / h : ℝ))) q‖ ≤
      (N.factorial : ℝ) * oscillatoryPhaseJetBound * A ^ N * h⁻¹ ^ N := by
  let g := fun y => phase y / h
  have hg : ContDiffAt ℝ ∞ g q := hp.div_const h
  have hD : 1 ≤ A * h⁻¹ := one_le_mul_of_one_le_of_one_le hA ((one_le_inv₀ hh).mpr hh₁)
  have hG (i : ℕ) (hi : 1 ≤ i) (hiN : i ≤ j) : ‖iteratedFDeriv ℝ i g q‖ ≤ (A*h⁻¹)^i := by
    have hEq : g = h⁻¹ • phase := by
      funext y
      simp [g,div_eq_mul_inv, mul_comm]
    rw [hEq,iteratedFDeriv_const_smul_apply (hp.of_le (by simp)),norm_smul,
      Real.norm_of_nonneg (inv_nonneg.mpr hh.le),mul_comm]
    refine (mul_le_mul_of_nonneg_right (hJet i hi (hiN.trans hj)) (inv_nonneg.mpr hh.le)).trans ?_
    simpa only [pow_one] using pow_le_pow_right₀ hD hi
  have hw := norm_iteratedFDeriv_comp_at_le g unitPhase q j hg unitPhase_contDiff.contDiffAt
    oscillatoryPhaseJetBound (A*h⁻¹) (fun i _ => unitPhase_iteratedFDeriv_norm i (g q)) hG
  have hFact : (j.factorial : ℝ) ≤ N.factorial := by exact_mod_cast Nat.factorial_le hj
  change ‖iteratedFDeriv ℝ j (unitPhase ∘ g) q‖ ≤ _
  calc
    _ ≤ (j.factorial : ℝ) * oscillatoryPhaseJetBound * (A * h⁻¹) ^ j := hw
    _ ≤ (N.factorial : ℝ) * oscillatoryPhaseJetBound * (A * h⁻¹) ^ N :=
      mul_le_mul (mul_le_mul_of_nonneg_right hFact oscillatoryPhaseJetBound_nonneg)
        (pow_le_pow_right₀ hD hj) (by positivity)
        (mul_nonneg (by positivity) oscillatoryPhaseJetBound_nonneg)
    _ = _ := by rw [mul_pow]; ring

end CalderonPaper
