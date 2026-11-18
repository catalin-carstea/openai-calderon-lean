import Proof.LegendreHilbert

noncomputable section
set_option autoImplicit false
open Set MeasureTheory MvPolynomial
open scoped InnerProductSpace
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.AngularPolynomial
open OAI.AnisotropicCalderon.SphereHarmonic

/-- The explicit physical degree kernel is the Hilbert projection of every continuous
    real fiber datum, in the same moving frame and probability sphere. -/
theorem degreePart_ofReal_harmonicProjection (g : MetricField) (e : Frame) (y : X)
    (hframe : ∀ i j,metricPair g y (e y i) (e y j) = if i = j then 1 else 0)
    (U : C(UnitSphere,ℝ)) (F : X → ℝ) (hF : ∀ v : UnitSphere,F (frameVector e y v.val) = U v)
    (v : UnitSphere) (k : ℕ) :
    degreePart g e k y (fun w => (F w : ℂ)) (frameVector e y v.val) =
      ((eval (v.val : I → ℝ) (harmonicProjectionPolynomial k (ContinuousMap.toLp 2 sphereProbability ℝ U)).val : ℝ) : ℂ) := by
  have hfun : (fun z : UnitSphere =>
      (legendre (metricPair g y (frameVector e y v.val) (frameVector e y z.val)) k : ℂ)*(F (frameVector e y z.val) : ℂ)) =
      fun z : UnitSphere => ((legendre (∑ i,v.val i*z.val i) k*U z : ℝ) : ℂ) := by
    funext z
    rw [metricPair_frameVector g e y v.val z.val hframe,hF z]
    exact (Complex.ofReal_mul _ _).symm
  change (((2*(k : ℝ)+1) : ℝ) : ℂ)*(∫ z : UnitSphere,
    (legendre (metricPair g y (frameVector e y v.val) (frameVector e y z.val)) k : ℂ)*(F (frameVector e y z.val) : ℂ) ∂sphereProbability) = _
  rw [hfun,integral_complex_ofReal]
  have hI : (∫ z : UnitSphere,legendre (∑ i,v.val i*z.val i) k*U z ∂sphereProbability) =
      ∫ z : UnitSphere,legendre (∑ i,v.val i*z.val i) k*(ContinuousMap.toLp 2 sphereProbability ℝ U) z ∂sphereProbability := by
    apply integral_congr_ae
    filter_upwards [U.coeFn_toLp (p:=2) (𝕜:=ℝ) sphereProbability] with z hz
    rw [hz]
  have hh := sphere_legendre_projection_Lp v k (ContinuousMap.toLp 2 sphereProbability ℝ U)
  rw [← hI] at hh
  simpa only [Complex.ofReal_mul] using congrArg Complex.ofReal hh

lemma fiberSq_degreePart_ofReal_harmonicProjection (g : MetricField) (e : Frame) (y : X)
    (hframe : ∀ i j,metricPair g y (e y i) (e y j) = if i = j then 1 else 0)
    (U : C(UnitSphere,ℝ)) (F : X → ℝ) (hF : ∀ v : UnitSphere,F (frameVector e y v.val) = U v) (k : ℕ) :
    fiberSq e y (degreePart g e k y (fun w => (F w : ℂ))) =
      ‖harmonicProjection k (ContinuousMap.toLp 2 sphereProbability ℝ U)‖^2 := by
  let p := harmonicProjectionPolynomial k (ContinuousMap.toLp 2 sphereProbability ℝ U)
  calc
    _ = fiberSq e y (fun w => (movingFramePolynomial g e p.val (y,w) : ℂ)) := by
      apply fiberSq_congr_frameVector
      intro v
      rw [degreePart_ofReal_harmonicProjection g e y hframe U F hF v k,
        movingFramePolynomial_frameVector g e y hframe]
    _ = normalizedFischerSquare k p.val := fiberSq_movingFramePolynomial g e y hframe _ p.property.1 p.property.2
    _ = _ := by
      rw [← polynomialSphereL2_norm_sq sphereFischerInner k p.val p.property]
      change ‖polynomialSphereL2 (harmonicProjectionPolynomial k (ContinuousMap.toLp 2 sphereProbability ℝ U)).val‖^2 = _
      rw [polynomialSphereL2_harmonicProjectionPolynomial]
      rfl

/-- The frozen Sobolev square is the weighted Hilbert coefficient norm for every continuous
    fiber datum; no finite-degree restriction is imposed. -/
theorem sobolevSq_ofReal_harmonicProjection (g : MetricField) (e : Frame) (y : X)
    (hframe : ∀ i j,metricPair g y (e y i) (e y j) = if i = j then 1 else 0)
    (U : C(UnitSphere,ℝ)) (F : X → ℝ) (hF : ∀ v : UnitSphere,F (frameVector e y v.val) = U v) (s : ℝ) :
    sobolevSq g e s y (fun w => (F w : ℂ)) =
      ∑' k : ℕ,(1+(k : ℝ))^(2*s)*‖harmonicProjection k (ContinuousMap.toLp 2 sphereProbability ℝ U)‖^2 := by
  unfold sobolevSq
  simp_rw [fiberSq_degreePart_ofReal_harmonicProjection g e y hframe U F hF]

end ShrinkingSpheres
