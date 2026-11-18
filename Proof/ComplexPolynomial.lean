import Proof.UniformFiniteCoercivity
import Proof.LegendreFiniteSum

noncomputable section
set_option autoImplicit false
open Set MeasureTheory MvPolynomial
open scoped ContDiff
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.AngularPolynomial
open OAI.AnisotropicCalderon.SphereHarmonic

/-- A complex harmonic polynomial is represented by its two real harmonic components. -/
def movingFrameComplexPolynomial (g : MetricField) (e : Frame) (p q : MvPolynomial I ℝ) (z : X × X) : ℂ :=
  Complex.mk (movingFramePolynomial g e p z) (movingFramePolynomial g e q z)

lemma fiberSq_integral_norm (e : Frame) (y : X) (u : X → ℂ) :
    fiberSq e y u = ∫ w : UnitSphere, ‖u (frameVector e y w.val)‖^2 ∂sphereProbability := by
  unfold fiberSq
  rw [sphereAverage_ofReal]
  rfl

lemma continuous_complexPolynomialSphere (p q : MvPolynomial I ℝ) :
    Continuous (fun w : UnitSphere => Complex.mk (eval (w.val : I → ℝ) p) (eval (w.val : I → ℝ) q)) := by
  exact Complex.equivRealProdCLM.symm.continuous.comp
    ((polynomialSphere p).continuous.prodMk (polynomialSphere q).continuous)

lemma integrable_complexPolynomialSphere (p q : MvPolynomial I ℝ) :
    Integrable (fun w : UnitSphere => Complex.mk (eval (w.val : I → ℝ) p) (eval (w.val : I → ℝ) q)) sphereProbability :=
  (continuous_complexPolynomialSphere p q).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

lemma integral_complexPolynomialSphere (p q : MvPolynomial I ℝ) :
    (∫ w : UnitSphere, Complex.mk (eval (w.val : I → ℝ) p) (eval (w.val : I → ℝ) q) ∂sphereProbability) =
      Complex.mk (∫ w : UnitSphere, eval (w.val : I → ℝ) p ∂sphereProbability)
        (∫ w : UnitSphere, eval (w.val : I → ℝ) q ∂sphereProbability) := by
  apply Complex.ext
  · exact (integral_re (integrable_complexPolynomialSphere p q)).symm
  · exact (integral_im (integrable_complexPolynomialSphere p q)).symm

/-- Exact physical fiber norm for a complex harmonic mode. -/
theorem fiberSq_movingFrameComplexPolynomial (g : MetricField) (e : Frame) (y : X)
    (hframe : ∀ i j, metricPair g y (e y i) (e y j) = if i = j then 1 else 0)
    {k : ℕ} (p q : MvPolynomial I ℝ) (hp : p.IsHomogeneous k) (hq : q.IsHomogeneous k)
    (hΔp : laplacian p = 0) (hΔq : laplacian q = 0) :
    fiberSq e y (fun w => movingFrameComplexPolynomial g e p q (y,w)) =
      normalizedFischerSquare k p + normalizedFischerSquare k q := by
  have hPInt : Integrable (fun w : UnitSphere => (eval (w.val : I → ℝ) p)^2) sphereProbability :=
    ((polynomialSphere p).continuous.pow 2).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hQInt : Integrable (fun w : UnitSphere => (eval (w.val : I → ℝ) q)^2) sphereProbability :=
    ((polynomialSphere q).continuous.pow 2).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hP := sphereFischerInner k p p ⟨hp,hΔp⟩ ⟨hp,hΔp⟩
  have hQ := sphereFischerInner k q q ⟨hq,hΔq⟩ ⟨hq,hΔq⟩
  rw [polynomialSphereL2_inner] at hP hQ
  rw [fiberSq_integral_norm]
  simp_rw [movingFrameComplexPolynomial, movingFramePolynomial_frameVector g e y hframe,
    Complex.sq_norm, Complex.normSq_mk]
  simp only [pow_two] at hPInt hQInt
  change (∫ w : UnitSphere, eval (w.val : I → ℝ) p * eval (w.val : I → ℝ) p +
    eval (w.val : I → ℝ) q * eval (w.val : I → ℝ) q ∂sphereProbability) = _
  rw [integral_add hPInt hQInt]
  simpa only [pow_two,normalizedFischerSquare] using congrArg₂ (· + ·) hP hQ

lemma horizontal_complexMk (g : MetricField) (F G : X × X → ℝ) (y w a : X)
    (hF : DifferentiableAt ℝ F (y,w)) (hG : DifferentiableAt ℝ G (y,w)) :
    horizontal g (fun z => Complex.mk (F z) (G z)) y w a =
      Complex.mk (horizontal (E:=ℝ) g F y w a) (horizontal (E:=ℝ) g G y w a) := by
  have hh := Complex.equivRealProdCLM.symm.toContinuousLinearMap.hasFDerivAt.comp (y,w)
    (hF.hasFDerivAt.prodMk hG.hasFDerivAt)
  change HasFDerivAt (fun z => Complex.mk (F z) (G z)) _ (y,w) at hh
  rw [horizontal, hh.fderiv]
  rfl

end ShrinkingSpheres
