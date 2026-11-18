import Proof.PhysicalLegendre

noncomputable section
set_option autoImplicit false
open Set MvPolynomial MeasureTheory
open scoped ContDiff
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.AngularPolynomial

variable {ι : Type*} [Fintype ι]

lemma sobolevSq_complexPolynomialField_weight (g : MetricField) (e : Frame) (y : X)
    (hframe : ∀ i j, metricPair g y (e y i) (e y j) = if i = j then 1 else 0)
    (s : ℝ) (k : ℕ) (b : ι → MvPolynomial I ℝ) (hb : ∀ a, (b a).IsHomogeneous k)
    (hΔ : ∀ a, laplacian (b a) = 0) (c : X → ι → ℝ) :
    sobolevSq g e s y (fun w => complexPolynomialField g e b c (y,w)) =
      (1+(k : ℝ))^(2*s) * fiberSq e y (fun w => complexPolynomialField g e b c (y,w)) := by
  rw [sobolevSq_complexPolynomialField g e y hframe s k b hb hΔ c,
    fiberSq_complexPolynomialField g e y hframe b hb hΔ c]

theorem sobolevSq_complexPolynomialField_horizontal_weight {Y : Set X} (hY : IsOpen Y) {K : ℝ} {g : MetricField}
    (h : Elliptic Y K g) (hK : 0 < K) (e : Frame)
    (he : ∀ i, ContDiffOn ℝ ∞ (fun x => e x i) Y)
    (hframe : ∀ y ∈ Y, ∀ i j, metricPair g y (e y i) (e y j) = if i = j then 1 else 0)
    (s : ℝ) {k : ℕ} (hk : 1 ≤ k) (b : ι → MvPolynomial I ℝ) (hb : ∀ a, (b a).IsHomogeneous k)
    (hΔ : ∀ a, laplacian (b a) = 0) (c : X → ι → ℝ) (hc : ContDiffOn ℝ ∞ c Y)
    {y : X} (hy : y ∈ Y) (i : I) :
    sobolevSq g e s y (fun w => horizontal g (complexPolynomialField g e b c) y w (e y i)) =
      (1+(k : ℝ))^(2*s) * fiberSq e y (fun w => horizontal g (complexPolynomialField g e b c) y w (e y i)) := by
  have hfun : (fun w => horizontal g (complexPolynomialField g e b c) y w (e y i)) =
      fun w => (movingFramePolynomial g e (covariantPolynomialDerivative g e b c y (e y i)) (y,w) : ℂ) := by
    funext w
    exact complexPolynomialField_horizontal hY h hK e he hframe b c hc hy w (e y i)
  have hp := covariantPolynomialDerivative_homogeneous hk g e b hb c y (e y i)
  have hΔp := covariantPolynomialDerivative_harmonic g e b hΔ c y (e y i)
    (frameConnection_skew hY h hK e he hframe hy (e y i))
  rw [hfun, sobolevSq_movingFramePolynomial g e y (hframe y hy) s k _ hp hΔp,
    fiberSq_movingFramePolynomial g e y (hframe y hy) _ hp hΔp]

/-- The frozen four-term Sobolev energy equals the physical degreewise energy on finite
    harmonic fields. Both the Legendre projection and horizontal derivative are identified. -/
theorem energySq_complexPolynomialField {Y : Set X} (hY : IsOpen Y) {K : ℝ} {g : MetricField}
    (h : Elliptic Y K g) (hK : 0 < K) (e : Frame)
    (he : ∀ i, ContDiffOn ℝ ∞ (fun x => e x i) Y)
    (hframe : ∀ y ∈ Y, ∀ i j, metricPair g y (e y i) (e y j) = if i = j then 1 else 0)
    (r : X → ℝ) {k : ℕ} (hk : 1 ≤ k) (b : ι → MvPolynomial I ℝ) (hb : ∀ a, (b a).IsHomogeneous k)
    (hΔ : ∀ a, laplacian (b a) = 0) (c : X → ι → ℝ) (hc : ContDiffOn ℝ ∞ c Y) :
    energySq Y g e r (complexPolynomialField g e b c) = sphereModeEnergy Y g e r k (complexPolynomialField g e b c) := by
  unfold energySq sphereModeEnergy
  apply setIntegral_congr_fun hY.measurableSet
  intro y hy
  dsimp only
  simp_rw [sobolevSq_complexPolynomialField_weight g e y (hframe y hy) _ k b hb hΔ c,
    sobolevSq_complexPolynomialField_horizontal_weight hY h hK e he hframe _ hk b hb hΔ c hc hy]
  norm_num only [mul_one, show (2 : ℝ)*(1/2) = 1 by norm_num,
    show (2 : ℝ)*(3/2) = 3 by norm_num, Real.rpow_one, Real.rpow_two,
    show (1+(k : ℝ))^(3 : ℝ) = (1+(k : ℝ))^3 from Real.rpow_natCast _ 3]
  simp only [sphereModeDensity, metricDensity, Finset.mul_sum]
  ring

/-- The full frozen energy for a positive finite harmonic degree is controlled by the
    genuine sphere raising-minus-lowering outputs. The curvature bound is explicit. -/
theorem Profile.energySq_finite_mode_coercive {Y : Set X} (hY : IsOpen Y) {K : ℝ} {g : MetricField}
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
    profileCoercivityConstant a c₀ * energySq Y g e r (complexPolynomialField g e b c) ≤
      outputSq Y g e (sphereRaisedField g e b c (fun x => Real.log (r x)) m) -
        outputSq Y g e (sphereLoweredField g e b c (fun x => Real.log (r x)) m) := by
  rw [energySq_complexPolynomialField hY h hK e he hframe r (by omega) b hb hΔ c hc.contDiffOn]
  exact hp.sphereModeEnergy_coercive hY h hK e he hframe hc₀ hfloor B hB hR hthreshold m b hb hΔ c hc hcompact hsupp a ha hasmall haf

end ShrinkingSpheres
