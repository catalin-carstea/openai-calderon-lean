module

public import Proof.Manuscript.MovingTrace.ParametricLayerProfiles
public import Mathlib.Tactic
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Pow

@[expose] public section

noncomputable section

open Polynomial Set Finset
open scoped ContDiff

namespace CalderonPatch.BoundaryLayer.ParametricLayerCoefficients

variable {n : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {U : Set E} (B : ParametricLayerCoefficients (n := n) U)

/-- Finite inward decaying trial wave with a normal cutoff. The real phase
can vary jointly with the base and frequency-direction parameters. -/
def finiteWave (a : E → ℂ) (η : ℝ → ℝ) (phase : E → ℝ) (M : ℕ) (h : ℝ)
    (q : E × ℝ) : ℂ :=
  Complex.exp (Complex.I * (phase q.1 / h : ℝ)) *
    ∑ j ∈ range (M + 1), (h ^ j : ℂ) * cutoffProfileFamily η B.kappa (B.layerPolynomial a j) h q

/-- The coefficients in the dephased inward normal derivative. The outer
normal derivative reverses their sign. -/
def traceCoefficient (a : E → ℂ) (j : ℕ) (y : E) : ℂ :=
  (profileDerivative (B.kappa y) (B.layerPolynomial a j y)).eval 0

theorem traceCoefficient_zero (a : E → ℂ) (y : E) :
    B.traceCoefficient a 0 y = -(B.kappa y : ℂ) * a y := by
  simp [traceCoefficient, B.layerPolynomial_zero, profileDerivative]

theorem traceCoefficient_eq_zero_of_notMem {K : Set E} (hU : IsOpen U)
    (hK : IsClosed K) (a : E → ℂ) (ha : ContDiffOn ℝ ∞ a U) (ha0 : ∀ y ∉ K, a y = 0)
    (j : ℕ) {y : E} (hy : y ∉ K) : B.traceCoefficient a j y = 0 := by
  rw [traceCoefficient, (B.layerPolynomial_properties hU hK a ha ha0 j).2.2 y hy]
  simp [profileDerivative]

theorem traceCoefficient_contDiffOn {K : Set E} (hU : IsOpen U)
    (hK : IsClosed K) (a : E → ℂ) (ha : ContDiffOn ℝ ∞ a U) (ha0 : ∀ y ∉ K, a y = 0)
    (j : ℕ) : ContDiffOn ℝ ∞ (B.traceCoefficient a j) U := by
  have hP := (B.layerPolynomial_properties hU hK a ha ha0 j).1
  have hκ := Complex.ofRealCLM.contDiff.comp_contDiffOn B.kappa_smooth
  have hD := hP.derivative.sub (hP.C_mul hκ)
  change ContDiffOn ℝ ∞ (fun y => (profileDerivative (B.kappa y) (B.layerPolynomial a j y)).eval 0) U
  simp only [← coeff_zero_eq_eval_zero]
  exact hD 0

theorem finiteWave_face (a : E → ℂ) (η : ℝ → ℝ) (hη : η 0 = 1)
    (phase : E → ℝ) (M : ℕ) (h : ℝ) (y : E) :
    B.finiteWave a η phase M h (y, 0) = Complex.exp (Complex.I * (phase y / h : ℝ)) * a y := by
  unfold finiteWave
  congr 1
  rw [sum_eq_single 0]
  · simp [cutoffProfileFamily, polynomialProfileFamily, hη, B.layerPolynomial_zero]
  · intro j hj hj₀
    simp [cutoffProfileFamily, polynomialProfileFamily, B.layerPolynomial_face_zero _ _ (Nat.pos_of_ne_zero hj₀)]
  · simp

theorem hasDerivAt_cutoffProfile_normal_generic
    (η : ℝ → ℝ) (hη : HasDerivAt η 0 0) (hη0 : η 0 = 1)
    (κ : E → ℝ) (P : E → ℂ[X]) (h : ℝ) (y : E) :
    HasDerivAt (fun t => cutoffProfileFamily η κ P h (y, t))
      ((profileDerivative (κ y) (P y)).eval 0 / (h : ℂ)) 0 := by
  have hp0 : HasDerivAt (polynomialProfile (κ y) (P y))
      (polynomialProfile (κ y) (profileDerivative (κ y) (P y)) 0) ((0 : ℝ) / h) := by
    simpa only [zero_div] using hasDerivAt_polynomialProfile (κ y) (P y) 0
  have hscale : HasDerivAt (fun t : ℝ => t / h) (1 / h) 0 := by
    simpa only [id_eq] using (hasDerivAt_id (0 : ℝ)).div_const h
  have hp := hp0.scomp 0 hscale
  have hp' : HasDerivAt (fun t : ℝ => polynomialProfile (κ y) (P y) (t / h))
      ((profileDerivative (κ y) (P y)).eval 0 / (h : ℂ)) 0 := by
    have he : (1 / h) • polynomialProfile (κ y) (profileDerivative (κ y) (P y)) 0 =
        ((profileDerivative (κ y) (P y)).eval 0 / (h : ℂ)) := by
      simp [polynomialProfile, Complex.real_smul, div_eq_mul_inv, mul_comm]
    rw [he] at hp
    exact hp
  change HasDerivAt (fun t : ℝ => η t • polynomialProfile (κ y) (P y) (t / h)) _ 0
  convert hη.smul hp' using 1 <;> simp only [hη0, one_smul, zero_smul, add_zero]

theorem hasDerivAt_finiteWave_normal (a : E → ℂ) (η : ℝ → ℝ) (hη : HasDerivAt η 0 0) (hη0 : η 0 = 1)
    (phase : E → ℝ) (M : ℕ) (h : ℝ) (y : E) :
    HasDerivAt (fun t => B.finiteWave a η phase M h (y, t))
      (Complex.exp (Complex.I * (phase y / h : ℝ)) *
        ((∑ j ∈ range (M + 1), (h ^ j : ℂ) * B.traceCoefficient a j y) / (h : ℂ))) 0 := by
  have hs : HasDerivAt
      (fun t : ℝ => ∑ j ∈ range (M + 1), (h ^ j : ℂ) *
        cutoffProfileFamily η B.kappa (B.layerPolynomial a j) h (y, t))
      (∑ j ∈ range (M + 1), (h ^ j : ℂ) * (B.traceCoefficient a j y / (h : ℂ))) 0 := by
    apply HasDerivAt.fun_sum
    intro j hj
    exact (hasDerivAt_cutoffProfile_normal_generic η hη hη0 B.kappa (B.layerPolynomial a j) h y).const_mul _
  convert hs.const_mul (Complex.exp (Complex.I * (phase y / h : ℝ))) using 1
  · rfl
  · simp only [← mul_div_assoc, sum_div]

theorem finiteWave_dephased_normal (a : E → ℂ) (η : ℝ → ℝ) (hη : HasDerivAt η 0 0) (hη0 : η 0 = 1)
    (phase : E → ℝ) (M : ℕ) (h : ℝ) (y : E) :
    (Complex.exp (Complex.I * (phase y / h : ℝ)))⁻¹ * deriv (fun t => B.finiteWave a η phase M h (y,t)) 0 =
      ∑ j ∈ range (M + 1), ((h : ℂ) ^ j / (h : ℂ)) * B.traceCoefficient a j y := by
  rw [(B.hasDerivAt_finiteWave_normal a η hη hη0 phase M h y).deriv, ← mul_assoc,
    inv_mul_cancel₀ (Complex.exp_ne_zero _), one_mul, sum_div]
  apply sum_congr rfl
  intro j _
  simp only [div_eq_mul_inv]
  ring

end CalderonPatch.BoundaryLayer.ParametricLayerCoefficients
