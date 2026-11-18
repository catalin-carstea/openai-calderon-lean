import Proof.TestHarmonicCoordinates

noncomputable section
set_option autoImplicit false
open Set MeasureTheory MvPolynomial Filter
open scoped InnerProductSpace
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.AngularPolynomial
open OAI.AnisotropicCalderon.SphereHarmonic

lemma integrable_complexMk {A : Type*} [MeasurableSpace A] {μ : Measure A} {f h : A → ℝ}
    (hf : Integrable f μ) (hh : Integrable h μ) : Integrable (fun x => Complex.mk (f x) (h x)) μ :=
  Complex.equivRealProdCLM.symm.toContinuousLinearMap.integrable_comp (hf.prodMk hh)

lemma integral_complexMk_of_integrable {A : Type*} [MeasurableSpace A] {μ : Measure A} {f h : A → ℝ}
    (hf : Integrable f μ) (hh : Integrable h μ) :
    (∫ x,Complex.mk (f x) (h x) ∂μ) = Complex.mk (∫ x,f x ∂μ) (∫ x,h x ∂μ) := by
  apply Complex.ext
  · exact (integral_re (integrable_complexMk hf hh)).symm
  · exact (integral_im (integrable_complexMk hf hh)).symm

lemma integrable_legendre_mul_Lp (v : UnitSphere) (k : ℕ) (u : SphereL2) :
    Integrable (fun z : UnitSphere => legendre (∑ i,v.val i*z.val i) k*u z) sphereProbability := by
  apply (L2.integrable_inner (𝕜:=ℝ) (polynomialSphereL2 (zonalPolynomial (v.val : I → ℝ) k)) u).congr
  filter_upwards [(polynomialSphere (zonalPolynomial (v.val : I → ℝ) k)).coeFn_toLp (p:=2) (𝕜:=ℝ) sphereProbability] with z hz
  change (polynomialSphereL2 (zonalPolynomial (v.val : I → ℝ) k)) z =
    eval (z.val : I → ℝ) (zonalPolynomial (v.val : I → ℝ) k) at hz
  rw [hz,eval_zonalPolynomial_unitSphere]
  simp only [RCLike.inner_apply,starRingEnd_apply,star_trivial,mul_comm]

/-- The physical complex kernel agrees with the projections of its two real L2 components.
    Almost-everywhere component identities suffice; no polynomial assumption is imposed. -/
theorem degreePart_harmonicProjection_components (g : MetricField) (e : Frame) (y : X)
    (hframe : ∀ i j,metricPair g y (e y i) (e y j) = if i = j then 1 else 0)
    (F : X → ℂ) (U V : SphereL2)
    (hRe : U =ᵐ[sphereProbability] (fun v : UnitSphere => (F (frameVector e y v.val)).re))
    (hIm : V =ᵐ[sphereProbability] (fun v : UnitSphere => (F (frameVector e y v.val)).im)) (w : UnitSphere) (k : ℕ) :
    degreePart g e k y F (frameVector e y w.val) =
      Complex.mk (eval (w.val : I → ℝ) (harmonicProjectionPolynomial k U).val)
        (eval (w.val : I → ℝ) (harmonicProjectionPolynomial k V).val) := by
  have hfun : (fun z : UnitSphere =>
      (legendre (metricPair g y (frameVector e y w.val) (frameVector e y z.val)) k : ℂ)*F (frameVector e y z.val)) =ᵐ[sphereProbability]
      fun z : UnitSphere => Complex.mk (legendre (∑ i,w.val i*z.val i) k*U z) (legendre (∑ i,w.val i*z.val i) k*V z) := by
    filter_upwards [hRe,hIm] with z hr hi
    rw [metricPair_frameVector g e y w.val z.val hframe]
    apply Complex.ext
    · simp only [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]
      rw [hr]
    · simp only [Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,zero_mul,add_zero]
      rw [hi]
  change (((2*(k : ℝ)+1) : ℝ) : ℂ)*(∫ z : UnitSphere,
    (legendre (metricPair g y (frameVector e y w.val) (frameVector e y z.val)) k : ℂ)*F (frameVector e y z.val) ∂sphereProbability) = _
  rw [integral_congr_ae hfun,integral_complexMk_of_integrable
    (integrable_legendre_mul_Lp w k U) (integrable_legendre_mul_Lp w k V),ofReal_mul_complexMk,
    sphere_legendre_projection_Lp w k U,sphere_legendre_projection_Lp w k V]

lemma normalizedFischerSquare_harmonicProjectionPolynomial (k : ℕ) (u : SphereL2) :
    normalizedFischerSquare k (harmonicProjectionPolynomial k u).val = ‖harmonicProjection k u‖^2 := by
  rw [← polynomialSphereL2_norm_sq sphereFischerInner k _ (harmonicProjectionPolynomial k u).property,
    polynomialSphereL2_harmonicProjectionPolynomial]
  rfl

lemma fiberSq_degreePart_harmonicProjection_components (g : MetricField) (e : Frame) (y : X)
    (hframe : ∀ i j,metricPair g y (e y i) (e y j) = if i = j then 1 else 0)
    (F : X → ℂ) (U V : SphereL2)
    (hRe : U =ᵐ[sphereProbability] (fun v : UnitSphere => (F (frameVector e y v.val)).re))
    (hIm : V =ᵐ[sphereProbability] (fun v : UnitSphere => (F (frameVector e y v.val)).im)) (k : ℕ) :
    fiberSq e y (degreePart g e k y F) = ‖harmonicProjection k U‖^2+‖harmonicProjection k V‖^2 := by
  calc
    _ = fiberSq e y (fun w => movingFrameComplexPolynomial g e
        (harmonicProjectionPolynomial k U).val (harmonicProjectionPolynomial k V).val (y,w)) := by
      apply fiberSq_congr_frameVector
      intro w
      rw [degreePart_harmonicProjection_components g e y hframe F U V hRe hIm w k,
        movingFrameComplexPolynomial_frameVector g e y hframe]
    _ = _ := by
      rw [fiberSq_movingFrameComplexPolynomial g e y hframe _ _
        (harmonicProjectionPolynomial k U).property.1 (harmonicProjectionPolynomial k V).property.1
        (harmonicProjectionPolynomial k U).property.2 (harmonicProjectionPolynomial k V).property.2,
        normalizedFischerSquare_harmonicProjectionPolynomial,normalizedFischerSquare_harmonicProjectionPolynomial]

/-- The exact frozen Sobolev square is the weighted harmonic coefficient square for every
    complex fiber datum with L2 components. The series is kept intact, so no summability
    hypothesis is silently used to split a real tsum. -/
theorem sobolevSq_harmonicProjection_components (g : MetricField) (e : Frame) (y : X)
    (hframe : ∀ i j,metricPair g y (e y i) (e y j) = if i = j then 1 else 0)
    (F : X → ℂ) (U V : SphereL2)
    (hRe : U =ᵐ[sphereProbability] (fun v : UnitSphere => (F (frameVector e y v.val)).re))
    (hIm : V =ᵐ[sphereProbability] (fun v : UnitSphere => (F (frameVector e y v.val)).im)) (s : ℝ) :
    sobolevSq g e s y F =
      ∑' k : ℕ,(1+(k : ℝ))^(2*s)*(‖harmonicProjection k U‖^2+‖harmonicProjection k V‖^2) := by
  unfold sobolevSq
  simp_rw [fiberSq_degreePart_harmonicProjection_components g e y hframe F U V hRe hIm]

lemma integral_square_L2 (u : SphereL2) :
    (∫ v : UnitSphere,(u v)^2 ∂sphereProbability) = ‖u‖^2 := by
  rw [← real_inner_self_eq_norm_sq,L2.inner_def]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun v => by
    simp only [RCLike.inner_apply,starRingEnd_apply,star_trivial,pow_two])

lemma integrable_square_L2 (u : SphereL2) : Integrable (fun v : UnitSphere => (u v)^2) sphereProbability := by
  simpa only [RCLike.inner_apply,starRingEnd_apply,star_trivial,pow_two] using
    L2.integrable_inner (𝕜:=ℝ) u u

/-- The physical fiber square of arbitrary L2 complex data is the sum of component squares. -/
theorem fiberSq_eq_component_norms (e : Frame) (y : X) (F : X → ℂ) (U V : SphereL2)
    (hRe : U =ᵐ[sphereProbability] (fun v : UnitSphere => (F (frameVector e y v.val)).re))
    (hIm : V =ᵐ[sphereProbability] (fun v : UnitSphere => (F (frameVector e y v.val)).im)) :
    fiberSq e y F = ‖U‖^2+‖V‖^2 := by
  rw [fiberSq_integral_norm]
  have heq : (fun v : UnitSphere => ‖F (frameVector e y v.val)‖^2) =ᵐ[sphereProbability]
      fun v : UnitSphere => (U v)^2+(V v)^2 := by
    filter_upwards [hRe,hIm] with v hr hi
    rw [Complex.sq_norm,Complex.normSq_apply,← hr,← hi]
    ring
  rw [integral_congr_ae heq,integral_add (integrable_square_L2 U) (integrable_square_L2 V),
    integral_square_L2,integral_square_L2]

end ShrinkingSpheres
