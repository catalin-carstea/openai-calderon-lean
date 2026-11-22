module

public import Proof.CalderonN.ZonalProjection
public import Proof.CalderonN.SphereFrame
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

import Mathlib.Tactic

public section

/- The two-component comparison ports ComplexHilbertProjection from
   the released Proposition 5.3 proof (f308cb9d). -/
noncomputable section
set_option autoImplicit false
open Set MeasureTheory MvPolynomial Filter
open scoped InnerProductSpace
namespace CalderonN

variable {n : ℕ}
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

private theorem ofReal_mul_complexMk (a b c : ℝ) :
    (a : ℂ) * Complex.mk b c = Complex.mk (a*b) (a*c) := by
  apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im]

variable [NeZero n]

lemma integrable_zonal_mul_Lp (v : UnitSphere n) (k : ℕ) (u : SphereL2 n) :
    Integrable (fun z : UnitSphere n => zonal n (∑ i,v.val i*z.val i) k*u z) (unitSphereProbability n) := by
  apply (L2.integrable_inner (𝕜:=ℝ) (polynomialSphereL2 (zonalPolynomial (v.val : I n → ℝ) k)) u).congr
  filter_upwards [(polynomialSphere (zonalPolynomial (v.val : I n → ℝ) k)).coeFn_toLp (p:=2) (𝕜:=ℝ) (unitSphereProbability n)] with z hz
  change (polynomialSphereL2 (zonalPolynomial (v.val : I n → ℝ) k)) z =
    eval (z.val : I n → ℝ) (zonalPolynomial (v.val : I n → ℝ) k) at hz
  rw [hz,eval_zonalPolynomial_of_unit _ _ (unitSphere_sum_sq z)]
  simp only [RCLike.inner_apply,starRingEnd_apply,star_trivial,mul_comm]

/-- The physical complex kernel agrees with the projections of its two real L2 components.
    Almost-everywhere component identities suffice; no polynomial assumption is imposed. -/
theorem degreePart_harmonicProjection_components (hn : 3 ≤ n) (g : MetricField n) (e : Frame n) (y : X n)
    (hframe : ∀ i j,metricPair g y (e y i) (e y j) = if i = j then 1 else 0)
    (F : X n → ℂ) (U V : SphereL2 n)
    (hRe : U =ᵐ[unitSphereProbability n] (fun v : UnitSphere n => (F (frameVector e y v.val)).re))
    (hIm : V =ᵐ[unitSphereProbability n] (fun v : UnitSphere n => (F (frameVector e y v.val)).im)) (w : UnitSphere n) (k : ℕ) :
    degreePart g e k y F (frameVector e y w.val) =
      Complex.mk (eval (w.val : I n → ℝ) (harmonicProjectionPolynomial k U).val)
        (eval (w.val : I n → ℝ) (harmonicProjectionPolynomial k V).val) := by
  have hfun : (fun z : UnitSphere n =>
      (zonal n (metricPair g y (frameVector e y w.val) (frameVector e y z.val)) k : ℂ)*F (frameVector e y z.val)) =ᵐ[unitSphereProbability n]
      fun z : UnitSphere n => Complex.mk (zonal n (∑ i,w.val i*z.val i) k*U z) (zonal n (∑ i,w.val i*z.val i) k*V z) := by
    filter_upwards [hRe,hIm] with z hr hi
    rw [metricPair_frameVector g e y w.val z.val hframe]
    apply Complex.ext
    · simp only [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]
      rw [hr]
    · simp only [Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,zero_mul,add_zero]
      rw [hi]
  change (harmonicMultiplicity n k : ℂ)*(∫ z : UnitSphere n,
    (zonal n (metricPair g y (frameVector e y w.val) (frameVector e y z.val)) k : ℂ)*F (frameVector e y z.val) ∂unitSphereProbability n) = _
  rw [integral_congr_ae hfun,integral_complexMk_of_integrable
    (integrable_zonal_mul_Lp w k U) (integrable_zonal_mul_Lp w k V),
    ← Complex.ofReal_natCast, ofReal_mul_complexMk,
    sphere_zonal_projection_Lp hn w k U,sphere_zonal_projection_Lp hn w k V]

omit [NeZero n] in
theorem fiberSq_eq_integral_norm_sq (e : Frame n) (y : X n) (u : X n → ℂ) :
    fiberSq e y u = ∫ w : UnitSphere n, ‖u (frameVector e y w.val)‖^2
      ∂unitSphereProbability n := by
  change (∫ w : UnitSphere n, ((‖u (frameVector e y w.val)‖^2 : ℝ) : ℂ)
    ∂unitSphereProbability n).re = _
  rw [integral_complex_ofReal, Complex.ofReal_re]

private theorem integrable_polynomialSphere_sq (p : MvPolynomial (Fin n) ℝ) :
    Integrable (fun w : UnitSphere n => (eval (w.val : I n → ℝ) p)^2)
      (unitSphereProbability n) :=
  ((polynomialSphere p).continuous.pow 2).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

private theorem integral_polynomialSphere_sq (p : MvPolynomial (Fin n) ℝ) :
    (∫ w : UnitSphere n, (eval (w.val : I n → ℝ) p)^2 ∂unitSphereProbability n) =
      ‖polynomialSphereL2 p‖ ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, polynomialSphereL2_inner]
  simp only [pow_two]

theorem fiberSq_degreePart_harmonicProjection_components (hn : 3 ≤ n) (g : MetricField n)
    (e : Frame n) (y : X n)
    (hframe : ∀ i j, metricPair g y (e y i) (e y j) = if i = j then 1 else 0)
    (F : X n → ℂ) (U V : SphereL2 n)
    (hRe : U =ᵐ[unitSphereProbability n] fun w : UnitSphere n => (F (frameVector e y w.val)).re)
    (hIm : V =ᵐ[unitSphereProbability n] fun w : UnitSphere n => (F (frameVector e y w.val)).im)
    (k : ℕ) :
    fiberSq e y (degreePart g e k y F) =
      ‖harmonicProjection k U‖^2 + ‖harmonicProjection k V‖^2 := by
  let p := (harmonicProjectionPolynomial k U).val
  let q := (harmonicProjectionPolynomial k V).val
  have hpoint (w : UnitSphere n) :
      ‖degreePart g e k y F (frameVector e y w.val)‖^2 =
        (eval (w.val : I n → ℝ) p)^2 + (eval (w.val : I n → ℝ) q)^2 := by
    rw [degreePart_harmonicProjection_components hn g e y hframe F U V hRe hIm w k,
      Complex.sq_norm, Complex.normSq_apply]
    simp only [pow_two, p, q]
  rw [fiberSq_eq_integral_norm_sq, integral_congr_ae (Filter.Eventually.of_forall hpoint),
    integral_add (integrable_polynomialSphere_sq p) (integrable_polynomialSphere_sq q),
    integral_polynomialSphere_sq p, integral_polynomialSphere_sq q]
  simp only [p, q, polynomialSphereL2_harmonicProjectionPolynomial]
  rfl

/-- The protected weighted norm is the sum of the squares of its two real
degree projections. This form keeps the weighted series intact. -/
theorem sobolevSq_harmonicProjection_components (hn : 3 ≤ n) (g : MetricField n) (e : Frame n)
    (y : X n)
    (hframe : ∀ i j, metricPair g y (e y i) (e y j) = if i = j then 1 else 0)
    (F : X n → ℂ) (U V : SphereL2 n)
    (hRe : U =ᵐ[unitSphereProbability n] fun w : UnitSphere n => (F (frameVector e y w.val)).re)
    (hIm : V =ᵐ[unitSphereProbability n] fun w : UnitSphere n => (F (frameVector e y w.val)).im)
    (s : ℝ) :
    sobolevSq g e s y F = ∑' k : ℕ, (1+(k : ℝ))^(2*s) *
      (‖harmonicProjection k U‖^2 + ‖harmonicProjection k V‖^2) := by
  unfold sobolevSq
  simp_rw [fiberSq_degreePart_harmonicProjection_components hn g e y hframe F U V hRe hIm]

end CalderonN
