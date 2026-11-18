import Proof.SphereModeEnergy

noncomputable section
set_option autoImplicit false
open Set MeasureTheory MvPolynomial
open scoped ContDiff
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.AngularPolynomial

variable {ι : Type*} [Fintype ι]

lemma raisedPolynomialField_homogeneous (g : MetricField) (e : Frame) (m : ℕ)
    (b : ι → MvPolynomial I ℝ) (hb : ∀ a, (b a).IsHomogeneous (m+1))
    (c : X → ι → ℝ) (f : X → ℝ) (y : X) :
    (raisedPolynomialField g e b c f m y).IsHomogeneous (m+2) := by
  have hq (i : I) : (weightedFramePolynomialField g e b c f (m+1) 1 y i).IsHomogeneous (m+1) := by
    simpa only [weightedFramePolynomialField, Nat.cast_add, Nat.cast_one] using
      weightedPolynomialDerivative_homogeneous (by omega) g e b hb c f 1 y (e y i)
  simpa only [raisedPolynomialField, polynomialSphereRaising, Nat.add_sub_cancel, Nat.add_assoc] using
    (harmonicRaising_isHomogeneous (k:=m+1) (by omega) _ hq).C_mul (2*(m : ℝ)+5)

lemma loweredPolynomialField_homogeneous (g : MetricField) (e : Frame) (m : ℕ)
    (b : ι → MvPolynomial I ℝ) (hb : ∀ a, (b a).IsHomogeneous (m+1))
    (c : X → ι → ℝ) (f : X → ℝ) (y : X) :
    (loweredPolynomialField g e b c f m y).IsHomogeneous m := by
  apply polynomialDivergence_isHomogeneous (k:=m+1) _
  intro i
  simpa only [weightedFramePolynomialField, Nat.cast_add, Nat.cast_one] using
    weightedPolynomialDerivative_homogeneous (by omega) g e b hb c f (-1) y (e y i)

lemma raisedPolynomialField_harmonic {Y : Set X} (hY : IsOpen Y) {K : ℝ} {g : MetricField}
    (h : Elliptic Y K g) (hK : 0 < K) (e : Frame)
    (he : ∀ i, ContDiffOn ℝ ∞ (fun x => e x i) Y)
    (hframe : ∀ y ∈ Y, ∀ i j, metricPair g y (e y i) (e y j) = if i = j then 1 else 0)
    (m : ℕ) (b : ι → MvPolynomial I ℝ) (hb : ∀ a, (b a).IsHomogeneous (m+1))
    (hΔ : ∀ a, laplacian (b a) = 0) (c : X → ι → ℝ) (f : X → ℝ) {y : X} (hy : y ∈ Y) :
    laplacian (raisedPolynomialField g e b c f m y) = 0 := by
  have hq (i : I) : (weightedFramePolynomialField g e b c f (m+1) 1 y i).IsHomogeneous (m+1) := by
    simpa only [weightedFramePolynomialField, Nat.cast_add, Nat.cast_one] using
      weightedPolynomialDerivative_homogeneous (by omega) g e b hb c f 1 y (e y i)
  have hh := laplacian_harmonicRaising (k:=m+1) _ hq
    (fun i => weightedFramePolynomialField_harmonic hY h hK e he hframe b hΔ c f (m+1) 1 hy i)
    (ne_of_gt (radiusSq_laplacian_coefficient_pos (σ:=I) m))
  simp only [Nat.add_sub_cancel] at hh
  simp only [raisedPolynomialField, polynomialSphereRaising, laplacian_C_mul, hh, mul_zero]

lemma loweredPolynomialField_harmonic {Y : Set X} (hY : IsOpen Y) {K : ℝ} {g : MetricField}
    (h : Elliptic Y K g) (hK : 0 < K) (e : Frame)
    (he : ∀ i, ContDiffOn ℝ ∞ (fun x => e x i) Y)
    (hframe : ∀ y ∈ Y, ∀ i j, metricPair g y (e y i) (e y j) = if i = j then 1 else 0)
    (m : ℕ) (b : ι → MvPolynomial I ℝ) (hΔ : ∀ a, laplacian (b a) = 0)
    (c : X → ι → ℝ) (f : X → ℝ) {y : X} (hy : y ∈ Y) :
    laplacian (loweredPolynomialField g e b c f m y) = 0 :=
  laplacian_polynomialDivergence _
    (fun i => weightedFramePolynomialField_harmonic hY h hK e he hframe b hΔ c f (m+1) (-1) hy i)

lemma raisedPolynomialField_zero_outside (g : MetricField) (e : Frame) (m : ℕ)
    (b : ι → MvPolynomial I ℝ) (c : X → ι → ℝ) (f : X → ℝ) {y : X} (hy : y ∉ tsupport c) :
    raisedPolynomialField g e b c f m y = 0 := by
  have hq : weightedFramePolynomialField g e b c f (m+1) 1 y = 0 := by
    funext i
    exact weightedPolynomialDerivative_zero_outside g e b c f (m+1) 1 hy (e y i)
  simp [raisedPolynomialField, hq, polynomialSphereRaising, harmonicRaising, polynomialRaising, polynomialDivergence]

lemma loweredPolynomialField_zero_outside (g : MetricField) (e : Frame) (m : ℕ)
    (b : ι → MvPolynomial I ℝ) (c : X → ι → ℝ) (f : X → ℝ) {y : X} (hy : y ∉ tsupport c) :
    loweredPolynomialField g e b c f m y = 0 := by
  have hq : weightedFramePolynomialField g e b c f (m+1) (-1) y = 0 := by
    funext i
    exact weightedPolynomialDerivative_zero_outside g e b c f (m+1) (-1) hy (e y i)
  simp [loweredPolynomialField, hq, polynomialDivergence]

def sphereRaisedField (g : MetricField) (e : Frame) (b : ι → MvPolynomial I ℝ)
    (c : X → ι → ℝ) (f : X → ℝ) (m : ℕ) : Field :=
  fun z => (movingFramePolynomial g e (raisedPolynomialField g e b c f m z.1) z : ℂ)

def sphereLoweredField (g : MetricField) (e : Frame) (b : ι → MvPolynomial I ℝ)
    (c : X → ι → ℝ) (f : X → ℝ) (m : ℕ) : Field :=
  fun z => (movingFramePolynomial g e (loweredPolynomialField g e b c f m z.1) z : ℂ)

theorem outputSq_sphereRaisedField {Y : Set X} (hY : IsOpen Y) {K : ℝ} {g : MetricField}
    (h : Elliptic Y K g) (hK : 0 < K) (e : Frame)
    (he : ∀ i, ContDiffOn ℝ ∞ (fun x => e x i) Y)
    (hframe : ∀ y ∈ Y, ∀ i j, metricPair g y (e y i) (e y j) = if i = j then 1 else 0)
    (m : ℕ) (b : ι → MvPolynomial I ℝ) (hb : ∀ a, (b a).IsHomogeneous (m+1))
    (hΔ : ∀ a, laplacian (b a) = 0) (c : X → ι → ℝ) (f : X → ℝ) (hsupp : tsupport c ⊆ Y) :
    outputSq Y g e (sphereRaisedField g e b c f m) = fischerRaisingEnergy g e b c f m := by
  unfold outputSq sphereRaisedField
  change (∫ y in Y, metricDensity g y * fiberSq e y
    (fun w => (movingFramePolynomial g e (raisedPolynomialField g e b c f m y) (y,w) : ℂ))) = _
  rw [setIntegral_congr_fun hY.measurableSet (fun y hy => congrArg (metricDensity g y * ·)
    (fiberSq_movingFramePolynomial g e y (hframe y hy) _
      (raisedPolynomialField_homogeneous g e m b hb c f y)
      (raisedPolynomialField_harmonic hY h hK e he hframe m b hb hΔ c f hy)))]
  apply setIntegral_eq_integral_of_forall_compl_eq_zero
  intro y hy
  simp [raisedPolynomialField_zero_outside g e m b c f (fun ht => hy (hsupp ht)),
    normalizedFischerSquare, normalizedFischerInner, fischerInner_zero_left]

theorem outputSq_sphereLoweredField {Y : Set X} (hY : IsOpen Y) {K : ℝ} {g : MetricField}
    (h : Elliptic Y K g) (hK : 0 < K) (e : Frame)
    (he : ∀ i, ContDiffOn ℝ ∞ (fun x => e x i) Y)
    (hframe : ∀ y ∈ Y, ∀ i j, metricPair g y (e y i) (e y j) = if i = j then 1 else 0)
    (m : ℕ) (b : ι → MvPolynomial I ℝ) (hb : ∀ a, (b a).IsHomogeneous (m+1))
    (hΔ : ∀ a, laplacian (b a) = 0) (c : X → ι → ℝ) (f : X → ℝ) (hsupp : tsupport c ⊆ Y) :
    outputSq Y g e (sphereLoweredField g e b c f m) = fischerLoweringEnergy g e b c f m := by
  unfold outputSq sphereLoweredField
  change (∫ y in Y, metricDensity g y * fiberSq e y
    (fun w => (movingFramePolynomial g e (loweredPolynomialField g e b c f m y) (y,w) : ℂ))) = _
  rw [setIntegral_congr_fun hY.measurableSet (fun y hy => congrArg (metricDensity g y * ·)
    (fiberSq_movingFramePolynomial g e y (hframe y hy) _
      (loweredPolynomialField_homogeneous g e m b hb c f y)
      (loweredPolynomialField_harmonic hY h hK e he hframe m b hΔ c f hy)))]
  apply setIntegral_eq_integral_of_forall_compl_eq_zero
  intro y hy
  simp [loweredPolynomialField_zero_outside g e m b c f (fun ht => hy (hsupp ht)),
    normalizedFischerSquare, normalizedFischerInner, fischerInner_zero_left]

/-- Finite degree coercivity in the physical sphere measure, uniformly for every admissible
    radius. Legendre projection and the trace-operator remainder are separate remaining steps. -/
theorem Profile.sphereModeEnergy_coercive {Y : Set X} (hY : IsOpen Y) {K : ℝ} {g : MetricField}
    (h : Elliptic Y K g) (hK : 0 < K) (e : Frame)
    (he : ∀ i, ContDiffOn ℝ ∞ (fun x => e x i) Y)
    (hframe : ∀ y ∈ Y, ∀ i j, metricPair g y (e y i) (e y j) = if i = j then 1 else 0)
    {r : X → ℝ} {floor c₀ : ℝ} {Cj : Fin 9 → ℝ} (hp : Profile Y g e r floor c₀ Cj)
    (hc₀ : 0 < c₀) (hfloor : 1 ≤ floor) (B : ℝ) (hB : 0 ≤ B)
    (hR : ∀ y ∈ Y, ∀ i j a b, |frameCurvatureCoefficient g e y (e y i) (e y j) a b| ≤ B)
    (hthreshold : 450*B ≤ c₀*floor) (m : ℕ) (b : ι → MvPolynomial I ℝ)
    (hb : ∀ j, (b j).IsHomogeneous (m+1)) (hΔ : ∀ j, laplacian (b j) = 0)
    (c : X → ι → ℝ) (hc : ContDiff ℝ ∞ c) (hcompact : HasCompactSupport c) (hsupp : tsupport c ⊆ Y)
    (a : ℝ) (ha : 0 < a) (hasmall : a ≤ c₀/8) (haf : a ≤ floor) :
    profileCoercivityConstant a c₀ * sphereModeEnergy Y g e r (m+1) (complexPolynomialField g e b c) ≤
      outputSq Y g e (sphereRaisedField g e b c (fun x => Real.log (r x)) m) -
        outputSq Y g e (sphereLoweredField g e b c (fun x => Real.log (r x)) m) := by
  rw [hp.sphereModeEnergy_eq_fischer hY h hK e he hframe hfloor (by omega) b hb hΔ c hc hcompact hsupp,
    outputSq_sphereRaisedField hY h hK e he hframe m b hb hΔ c _ hsupp,
    outputSq_sphereLoweredField hY h hK e he hframe m b hb hΔ c _ hsupp]
  exact hp.modeFischerEnergy_coercive_of_curvature_bound hY h hK e he hframe hc₀ hfloor B hB hR hthreshold m b hb hΔ c hc hcompact hsupp a ha hasmall haf

end ShrinkingSpheres
