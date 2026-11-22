module

public import Proof.CalderonN.PhysicalModeCoercivity

import Mathlib.Tactic

@[expose] public section

noncomputable section
set_option autoImplicit false
open Set MeasureTheory MvPolynomial
open scoped ContDiff
namespace CalderonN
variable {n : ℕ} [NeZero n]
open OAI.AnisotropicCalderon.AngularPolynomial
open OAI.AnisotropicCalderon.SphereHarmonic

/-- A complex harmonic polynomial is represented by its two real harmonic components. -/
def movingFrameComplexPolynomial (g : (MetricField n)) (e : (Frame n)) (p q : MvPolynomial (I n) ℝ) (z : (X n) × (X n)) : ℂ :=
  Complex.mk (movingFramePolynomial g e p z) (movingFramePolynomial g e q z)

/-- Exact physical fiber norm for a complex harmonic mode. -/
theorem fiberSq_movingFrameComplexPolynomial (g : (MetricField n)) (e : (Frame n)) (y : (X n))
    (hframe : ∀ i j, metricPair g y (e y i) (e y j) = if i = j then 1 else 0)
    {k : ℕ} (p q : MvPolynomial (I n) ℝ) (hp : p.IsHomogeneous k) (hq : q.IsHomogeneous k)
    (hΔp : laplacian p = 0) (hΔq : laplacian q = 0) :
    fiberSq e y (fun w => movingFrameComplexPolynomial g e p q (y,w)) =
      normalizedFischerSquare k p + normalizedFischerSquare k q := by
  have hPInt : Integrable (fun w : (UnitSphere n) => (eval (w.val : (I n) → ℝ) p)^2) (unitSphereProbability n) :=
    ((polynomialSphere p).continuous.pow 2).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hQInt : Integrable (fun w : (UnitSphere n) => (eval (w.val : (I n) → ℝ) q)^2) (unitSphereProbability n) :=
    ((polynomialSphere q).continuous.pow 2).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hP := sphereFischerInner n k p p ⟨hp,hΔp⟩ ⟨hp,hΔp⟩
  have hQ := sphereFischerInner n k q q ⟨hq,hΔq⟩ ⟨hq,hΔq⟩
  rw [polynomialSphereL2_inner] at hP hQ
  rw [fiberSq_eq_integral_norm_sq]
  simp_rw [movingFrameComplexPolynomial, movingFramePolynomial_frameVector g e y hframe,
    Complex.sq_norm, Complex.normSq_mk]
  simp only [pow_two] at hPInt hQInt
  change (∫ w : (UnitSphere n), eval (w.val : (I n) → ℝ) p * eval (w.val : (I n) → ℝ) p +
    eval (w.val : (I n) → ℝ) q * eval (w.val : (I n) → ℝ) q ∂(unitSphereProbability n)) = _
  rw [integral_add hPInt hQInt]
  simpa only [pow_two,normalizedFischerSquare] using congrArg₂ (· + ·) hP hQ

lemma horizontal_complexMk (g : (MetricField n)) (F G : (X n) × (X n) → ℝ) (y w a : (X n))
    (hF : DifferentiableAt ℝ F (y,w)) (hG : DifferentiableAt ℝ G (y,w)) :
    horizontal g (fun z => Complex.mk (F z) (G z)) y w a =
      Complex.mk (horizontal (E:=ℝ) g F y w a) (horizontal (E:=ℝ) g G y w a) := by
  have hh := Complex.equivRealProdCLM.symm.toContinuousLinearMap.hasFDerivAt.comp (y,w)
    (hF.hasFDerivAt.prodMk hG.hasFDerivAt)
  change HasFDerivAt (fun z => Complex.mk (F z) (G z)) _ (y,w) at hh
  rw [horizontal, hh.fderiv]
  rfl

end CalderonN
