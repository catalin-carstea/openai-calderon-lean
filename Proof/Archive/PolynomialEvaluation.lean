module

public import Proof.Archive.HarmonicRaising
public import Mathlib.Analysis.Calculus.FDeriv.Prod
public import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Tactic

@[expose] public section

/- Selected evaluation-differentiation lemmas from the supplied GreenRadialTrace.lean. -/
noncomputable section
namespace OAI.AnisotropicCalderon.GreenRadialTrace
open MvPolynomial
open OAI.AnisotropicCalderon.AngularPolynomial
variable {σ : Type*} [Fintype σ] [DecidableEq σ]

 
def polynomialFDeriv (p : MvPolynomial σ ℝ) (z : σ → ℝ) : (σ → ℝ) →L[ℝ] ℝ :=
  ∑ i : σ, (ContinuousLinearMap.proj i).smulRight (eval z (pderiv i p))

lemma polynomialFDeriv_apply (p : MvPolynomial σ ℝ) (z v : σ → ℝ) :
    polynomialFDeriv p z v = ∑ i : σ, v i * eval z (pderiv i p) := by
  simp [polynomialFDeriv, smul_eq_mul]

lemma polynomialFDeriv_C (c : ℝ) (z : σ → ℝ) :
    polynomialFDeriv (C c) z = 0 := by
  simp [polynomialFDeriv]

lemma polynomialFDeriv_add (p q : MvPolynomial σ ℝ) (z : σ → ℝ) :
    polynomialFDeriv (p + q) z = polynomialFDeriv p z + polynomialFDeriv q z := by
  ext v
  simp [polynomialFDeriv_apply, map_add, mul_add, Finset.sum_add_distrib]

lemma polynomialFDeriv_mul (p q : MvPolynomial σ ℝ) (z : σ → ℝ) :
    polynomialFDeriv (p * q) z =
      eval z p • polynomialFDeriv q z + eval z q • polynomialFDeriv p z := by
  ext v
  simp only [polynomialFDeriv_apply, add_apply,
    smul_apply, smul_eq_mul, pderiv_mul, map_add, map_mul]
  simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  ring

lemma polynomialFDeriv_X (j : σ) (z : σ → ℝ) :
    polynomialFDeriv (X j) z = ContinuousLinearMap.proj j := by
  classical
  ext v
  simp [polynomialFDeriv_apply, pderiv_X, Pi.single_apply, mul_ite]

 
theorem hasFDerivAt_eval (p : MvPolynomial σ ℝ) (z : σ → ℝ) :
    HasFDerivAt (fun x : σ → ℝ => eval x p) (polynomialFDeriv p z) z := by
  induction p using MvPolynomial.induction_on with
  | C c =>
    rw [polynomialFDeriv_C]
    simpa only [eval_C] using hasFDerivAt_const (𝕜 := ℝ) c z
  | add p q hp hq =>
    rw [polynomialFDeriv_add]
    convert! hp.add hq using 1 <;> ext x <;> simp
  | mul_X p j hp =>
    rw [polynomialFDeriv_mul, polynomialFDeriv_X, eval_X]
    convert! hp.mul (hasFDerivAt_apply j z) using 1 <;> ext x <;> simp

lemma fderiv_eval_apply (p : MvPolynomial σ ℝ) (z v : σ → ℝ) :
    fderiv ℝ (fun x : σ → ℝ => eval x p) z v =
      ∑ i : σ, v i * eval z (pderiv i p) := by
  rw [(hasFDerivAt_eval p z).fderiv, polynomialFDeriv_apply]

end OAI.AnisotropicCalderon.GreenRadialTrace
