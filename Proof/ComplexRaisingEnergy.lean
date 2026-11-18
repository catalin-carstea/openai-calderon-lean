import Proof.ComplexFiniteEnergy

noncomputable section
set_option autoImplicit false
open Set MeasureTheory MvPolynomial
open scoped ContDiff
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.AngularPolynomial

variable {ι : Type*} [Fintype ι]

def pairedRaisedField (g : MetricField) (e : Frame) (b : ι → MvPolynomial I ℝ)
    (c d : X → ι → ℝ) (f : X → ℝ) (m : ℕ) : Field := fun z =>
  movingFrameComplexPolynomial g e (raisedPolynomialField g e b c f m z.1) (raisedPolynomialField g e b d f m z.1) z

def pairedLoweredField (g : MetricField) (e : Frame) (b : ι → MvPolynomial I ℝ)
    (c d : X → ι → ℝ) (f : X → ℝ) (m : ℕ) : Field := fun z =>
  movingFrameComplexPolynomial g e (loweredPolynomialField g e b c f m z.1) (loweredPolynomialField g e b d f m z.1) z

lemma outputSq_pairedRaisedField {Y : Set X} (hY : IsOpen Y) {K : ℝ} {g : MetricField}
    (h : Elliptic Y K g) (hK : 0 < K) (e : Frame)
    (he : ∀ i, ContDiffOn ℝ ∞ (fun x => e x i) Y)
    (hframe : ∀ y ∈ Y, ∀ i j, metricPair g y (e y i) (e y j) = if i = j then 1 else 0)
    (m : ℕ) (b : ι → MvPolynomial I ℝ) (hb : ∀ j, (b j).IsHomogeneous (m+1))
    (hΔ : ∀ j, laplacian (b j) = 0) (c d : X → ι → ℝ) (hc : ContDiff ℝ ∞ c) (hd : ContDiff ℝ ∞ d)
    (hcompactc : HasCompactSupport c) (hcompactd : HasCompactSupport d) (hsuppc : tsupport c ⊆ Y) (hsuppd : tsupport d ⊆ Y)
    (f : X → ℝ) (hf : ContDiffOn ℝ ∞ f Y) :
    outputSq Y g e (pairedRaisedField g e b c d f m) = fischerRaisingEnergy g e b c f m + fischerRaisingEnergy g e b d f m := by
  unfold outputSq pairedRaisedField
  change (∫ y in Y, metricDensity g y * fiberSq e y (fun w => movingFrameComplexPolynomial g e
    (raisedPolynomialField g e b c f m y) (raisedPolynomialField g e b d f m y) (y,w))) = _
  rw [setIntegral_congr_fun hY.measurableSet (fun y hy => congrArg (metricDensity g y * ·)
    (fiberSq_movingFrameComplexPolynomial g e y (hframe y hy) _ _
      (raisedPolynomialField_homogeneous g e m b hb c f y) (raisedPolynomialField_homogeneous g e m b hb d f y)
      (raisedPolynomialField_harmonic hY h hK e he hframe m b hb hΔ c f hy)
      (raisedPolynomialField_harmonic hY h hK e he hframe m b hb hΔ d f hy)))]
  simp_rw [mul_add]
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero (fun y hy => by
    simp [raisedPolynomialField_zero_outside g e m b c f (fun ht => hy (hsuppc ht)),
      raisedPolynomialField_zero_outside g e m b d f (fun ht => hy (hsuppd ht)),
      normalizedFischerSquare, normalizedFischerInner, fischerInner_zero_left])]
  rw [integral_add (integrable_fischerRaisingEnergy hY h hK e he b c f m hc hf hcompactc hsuppc)
    (integrable_fischerRaisingEnergy hY h hK e he b d f m hd hf hcompactd hsuppd)]
  rfl

lemma outputSq_pairedLoweredField {Y : Set X} (hY : IsOpen Y) {K : ℝ} {g : MetricField}
    (h : Elliptic Y K g) (hK : 0 < K) (e : Frame)
    (he : ∀ i, ContDiffOn ℝ ∞ (fun x => e x i) Y)
    (hframe : ∀ y ∈ Y, ∀ i j, metricPair g y (e y i) (e y j) = if i = j then 1 else 0)
    (m : ℕ) (b : ι → MvPolynomial I ℝ) (hb : ∀ j, (b j).IsHomogeneous (m+1))
    (hΔ : ∀ j, laplacian (b j) = 0) (c d : X → ι → ℝ) (hc : ContDiff ℝ ∞ c) (hd : ContDiff ℝ ∞ d)
    (hcompactc : HasCompactSupport c) (hcompactd : HasCompactSupport d) (hsuppc : tsupport c ⊆ Y) (hsuppd : tsupport d ⊆ Y)
    (f : X → ℝ) (hf : ContDiffOn ℝ ∞ f Y) :
    outputSq Y g e (pairedLoweredField g e b c d f m) = fischerLoweringEnergy g e b c f m + fischerLoweringEnergy g e b d f m := by
  unfold outputSq pairedLoweredField
  change (∫ y in Y, metricDensity g y * fiberSq e y (fun w => movingFrameComplexPolynomial g e
    (loweredPolynomialField g e b c f m y) (loweredPolynomialField g e b d f m y) (y,w))) = _
  rw [setIntegral_congr_fun hY.measurableSet (fun y hy => congrArg (metricDensity g y * ·)
    (fiberSq_movingFrameComplexPolynomial g e y (hframe y hy) _ _
      (loweredPolynomialField_homogeneous g e m b hb c f y) (loweredPolynomialField_homogeneous g e m b hb d f y)
      (loweredPolynomialField_harmonic hY h hK e he hframe m b hΔ c f hy)
      (loweredPolynomialField_harmonic hY h hK e he hframe m b hΔ d f hy)))]
  simp_rw [mul_add]
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero (fun y hy => by
    simp [loweredPolynomialField_zero_outside g e m b c f (fun ht => hy (hsuppc ht)),
      loweredPolynomialField_zero_outside g e m b d f (fun ht => hy (hsuppd ht)),
      normalizedFischerSquare, normalizedFischerInner, fischerInner_zero_left])]
  rw [integral_add (integrable_fischerLoweringEnergy hY h hK e he b c f m hc hf hcompactc hsuppc)
    (integrable_fischerLoweringEnergy hY h hK e he b d f m hd hf hcompactd hsuppd)]
  rfl

/-- Complex finite-mode coercivity in the exact frozen energy and output squares. -/
theorem Profile.energySq_paired_mode_coercive {Y : Set X} (hY : IsOpen Y) {K : ℝ} {g : MetricField}
    (h : Elliptic Y K g) (hK : 0 < K) (e : Frame)
    (he : ∀ i, ContDiffOn ℝ ∞ (fun x => e x i) Y)
    (hframe : ∀ y ∈ Y, ∀ i j, metricPair g y (e y i) (e y j) = if i = j then 1 else 0)
    {r : X → ℝ} {floor c₀ : ℝ} {Cj : Fin 9 → ℝ} (hp : Profile Y g e r floor c₀ Cj)
    (hc₀ : 0 < c₀) (hfloor : 1 ≤ floor) (B : ℝ) (hB : 0 ≤ B)
    (hR : ∀ y ∈ Y, ∀ i j a b, |frameCurvatureCoefficient g e y (e y i) (e y j) a b| ≤ B)
    (hthreshold : 450*B ≤ c₀*floor) (m : ℕ) (b : ι → MvPolynomial I ℝ)
    (hb : ∀ j, (b j).IsHomogeneous (m+1)) (hΔ : ∀ j, laplacian (b j) = 0)
    (c d : X → ι → ℝ) (hc : ContDiff ℝ ∞ c) (hd : ContDiff ℝ ∞ d)
    (hcompactc : HasCompactSupport c) (hcompactd : HasCompactSupport d) (hsuppc : tsupport c ⊆ Y) (hsuppd : tsupport d ⊆ Y)
    (a : ℝ) (ha : 0 < a) (hasmall : a ≤ c₀/8) (haf : a ≤ floor) :
    profileCoercivityConstant a c₀ * energySq Y g e r (pairedPolynomialField g e b c d) ≤
      outputSq Y g e (pairedRaisedField g e b c d (fun x => Real.log (r x)) m) -
        outputSq Y g e (pairedLoweredField g e b c d (fun x => Real.log (r x)) m) := by
  have hf := hp.1.log (fun y hy => (hp.2 y hy).1.ne')
  rw [hp.energySq_pairedPolynomialField hY h hK e he hframe hfloor (by omega) b hb hΔ c d hc hd hcompactc hcompactd hsuppc hsuppd,
    outputSq_pairedRaisedField hY h hK e he hframe m b hb hΔ c d hc hd hcompactc hcompactd hsuppc hsuppd _ hf,
    outputSq_pairedLoweredField hY h hK e he hframe m b hb hΔ c d hc hd hcompactc hcompactd hsuppc hsuppd _ hf]
  have hc' := hp.modeFischerEnergy_coercive_of_curvature_bound hY h hK e he hframe hc₀ hfloor B hB hR hthreshold m b hb hΔ c hc hcompactc hsuppc a ha hasmall haf
  have hd' := hp.modeFischerEnergy_coercive_of_curvature_bound hY h hK e he hframe hc₀ hfloor B hB hR hthreshold m b hb hΔ d hd hcompactd hsuppd a ha hasmall haf
  have hh := add_le_add hc' hd'
  rw [add_div, mul_add]
  linarith only [hh]

end ShrinkingSpheres
