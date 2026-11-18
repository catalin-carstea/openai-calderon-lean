import Proof.ComplexFiniteFields

noncomputable section
set_option autoImplicit false
open Set MeasureTheory MvPolynomial
open scoped ContDiff
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.AngularPolynomial

variable {ι : Type*} [Fintype ι]

lemma sobolevSq_pairedPolynomialField_weight (g : MetricField) (e : Frame) (y : X)
    (hframe : ∀ i j, metricPair g y (e y i) (e y j) = if i = j then 1 else 0)
    (s : ℝ) (k : ℕ) (b : ι → MvPolynomial I ℝ) (hb : ∀ a, (b a).IsHomogeneous k)
    (hΔ : ∀ a, laplacian (b a) = 0) (c d : X → ι → ℝ) :
    sobolevSq g e s y (fun w => pairedPolynomialField g e b c d (y,w)) =
      (1+(k : ℝ))^(2*s) * fiberSq e y (fun w => pairedPolynomialField g e b c d (y,w)) := by
  change sobolevSq g e s y (fun w => movingFrameComplexPolynomial g e
    (finitePolynomialField b c y) (finitePolynomialField b d y) (y,w)) = _
  rw [sobolevSq_movingFrameComplexPolynomial g e y hframe s k _ _
    (finitePolynomialField_homogeneous b hb c y) (finitePolynomialField_homogeneous b hb d y)
    (finitePolynomialField_harmonic b hΔ c y) (finitePolynomialField_harmonic b hΔ d y),
    fiberSq_pairedPolynomialField g e y hframe b hb hΔ c d]

lemma sobolevSq_pairedPolynomialField_horizontal_weight {Y : Set X} (hY : IsOpen Y) {K : ℝ} {g : MetricField}
    (h : Elliptic Y K g) (hK : 0 < K) (e : Frame)
    (he : ∀ i, ContDiffOn ℝ ∞ (fun x => e x i) Y)
    (hframe : ∀ y ∈ Y, ∀ i j, metricPair g y (e y i) (e y j) = if i = j then 1 else 0)
    (s : ℝ) {k : ℕ} (hk : 1 ≤ k) (b : ι → MvPolynomial I ℝ) (hb : ∀ a, (b a).IsHomogeneous k)
    (hΔ : ∀ a, laplacian (b a) = 0) (c d : X → ι → ℝ) (hc : ContDiffOn ℝ ∞ c Y) (hd : ContDiffOn ℝ ∞ d Y)
    {y : X} (hy : y ∈ Y) (i : I) :
    sobolevSq g e s y (fun w => horizontal g (pairedPolynomialField g e b c d) y w (e y i)) =
      (1+(k : ℝ))^(2*s)*fiberSq e y (fun w => horizontal g (pairedPolynomialField g e b c d) y w (e y i)) := by
  have hfun : (fun w => horizontal g (pairedPolynomialField g e b c d) y w (e y i)) =
      fun w => movingFrameComplexPolynomial g e (covariantPolynomialDerivative g e b c y (e y i))
        (covariantPolynomialDerivative g e b d y (e y i)) (y,w) := by
    funext w
    exact pairedPolynomialField_horizontal hY h hK e he hframe b c d hc hd hy w (e y i)
  have hpc := covariantPolynomialDerivative_homogeneous hk g e b hb c y (e y i)
  have hpd := covariantPolynomialDerivative_homogeneous hk g e b hb d y (e y i)
  have hΔc := covariantPolynomialDerivative_harmonic g e b hΔ c y (e y i) (frameConnection_skew hY h hK e he hframe hy (e y i))
  have hΔd := covariantPolynomialDerivative_harmonic g e b hΔ d y (e y i) (frameConnection_skew hY h hK e he hframe hy (e y i))
  rw [hfun, sobolevSq_movingFrameComplexPolynomial g e y (hframe y hy) s k _ _ hpc hpd hΔc hΔd,
    fiberSq_movingFrameComplexPolynomial g e y (hframe y hy) _ _ hpc hpd hΔc hΔd]

lemma sphereModeDensity_pairedPolynomialField {Y : Set X} (hY : IsOpen Y) {K : ℝ} {g : MetricField}
    (h : Elliptic Y K g) (hK : 0 < K) (e : Frame)
    (he : ∀ i, ContDiffOn ℝ ∞ (fun x => e x i) Y)
    (hframe : ∀ y ∈ Y, ∀ i j, metricPair g y (e y i) (e y j) = if i = j then 1 else 0)
    (r : X → ℝ) {k : ℕ} (hk : 1 ≤ k) (b : ι → MvPolynomial I ℝ) (hb : ∀ a, (b a).IsHomogeneous k)
    (hΔ : ∀ a, laplacian (b a) = 0) (c d : X → ι → ℝ) (hc : ContDiffOn ℝ ∞ c Y) (hd : ContDiffOn ℝ ∞ d Y)
    {y : X} (hy : y ∈ Y) :
    sphereModeDensity g e r k (pairedPolynomialField g e b c d) y =
      (modeFischerDensity g e r k b c y+modeFischerDensity g e r k b d y)/sphereNormalization 3 k := by
  have hV := fiberSq_pairedPolynomialField g e y (hframe y hy) b hb hΔ c d
  have hH : (∑ i, fiberSq e y (fun w => horizontal g (pairedPolynomialField g e b c d) y w (e y i))) =
      (covariantFrameEnergy g e b c y+covariantFrameEnergy g e b d y)/sphereNormalization 3 k := by
    simp_rw [fiberSq_pairedPolynomialField_horizontal hY h hK e he hframe hk b hb hΔ c d hc hd hy]
    simp only [normalizedFischerSquare, normalizedFischerInner, Fintype.card_fin, covariantFrameEnergy,
      Finset.sum_add_distrib, Finset.sum_div, add_div]
  simp only [sphereModeDensity, hV, hH, normalizedFischerSquare, normalizedFischerInner,
    Fintype.card_fin, modeFischerDensity]
  ring

lemma energySq_pairedPolynomialField_eq_sphereModeEnergy {Y : Set X} (hY : IsOpen Y) {K : ℝ} {g : MetricField}
    (h : Elliptic Y K g) (hK : 0 < K) (e : Frame)
    (he : ∀ i, ContDiffOn ℝ ∞ (fun x => e x i) Y)
    (hframe : ∀ y ∈ Y, ∀ i j, metricPair g y (e y i) (e y j) = if i = j then 1 else 0)
    (r : X → ℝ) {k : ℕ} (hk : 1 ≤ k) (b : ι → MvPolynomial I ℝ) (hb : ∀ a, (b a).IsHomogeneous k)
    (hΔ : ∀ a, laplacian (b a) = 0) (c d : X → ι → ℝ) (hc : ContDiffOn ℝ ∞ c Y) (hd : ContDiffOn ℝ ∞ d Y) :
    energySq Y g e r (pairedPolynomialField g e b c d) = sphereModeEnergy Y g e r k (pairedPolynomialField g e b c d) := by
  unfold energySq sphereModeEnergy
  apply setIntegral_congr_fun hY.measurableSet
  intro y hy
  dsimp only
  simp_rw [sobolevSq_pairedPolynomialField_weight g e y (hframe y hy) _ k b hb hΔ c d,
    sobolevSq_pairedPolynomialField_horizontal_weight hY h hK e he hframe _ hk b hb hΔ c d hc hd hy]
  norm_num only [mul_one, show (2 : ℝ)*(1/2) = 1 by norm_num,
    show (2 : ℝ)*(3/2) = 3 by norm_num, Real.rpow_one, Real.rpow_two,
    show (1+(k : ℝ))^(3 : ℝ) = (1+(k : ℝ))^3 from Real.rpow_natCast _ 3]
  simp only [sphereModeDensity, metricDensity, Finset.mul_sum]
  ring

/-- Exact full frozen energy for a compact complex harmonic field. -/
theorem Profile.energySq_pairedPolynomialField {Y : Set X} (hY : IsOpen Y) {K : ℝ} {g : MetricField}
    (h : Elliptic Y K g) (hK : 0 < K) (e : Frame)
    (he : ∀ i, ContDiffOn ℝ ∞ (fun x => e x i) Y)
    (hframe : ∀ y ∈ Y, ∀ i j, metricPair g y (e y i) (e y j) = if i = j then 1 else 0)
    {r : X → ℝ} {floor c₀ : ℝ} {Cj : Fin 9 → ℝ} (hp : Profile Y g e r floor c₀ Cj) (hfloor : 1 ≤ floor)
    {k : ℕ} (hk : 1 ≤ k) (b : ι → MvPolynomial I ℝ) (hb : ∀ a, (b a).IsHomogeneous k)
    (hΔ : ∀ a, laplacian (b a) = 0) (c d : X → ι → ℝ) (hc : ContDiff ℝ ∞ c) (hd : ContDiff ℝ ∞ d)
    (hcompactc : HasCompactSupport c) (hcompactd : HasCompactSupport d) (hsuppc : tsupport c ⊆ Y) (hsuppd : tsupport d ⊆ Y) :
    energySq Y g e r (pairedPolynomialField g e b c d) =
      (profileModeFischerEnergy g e r k b c+profileModeFischerEnergy g e r k b d)/sphereNormalization 3 k := by
  rw [energySq_pairedPolynomialField_eq_sphereModeEnergy hY h hK e he hframe _ hk b hb hΔ c d hc.contDiffOn hd.contDiffOn]
  unfold sphereModeEnergy
  rw [setIntegral_congr_fun hY.measurableSet (fun y hy =>
    sphereModeDensity_pairedPolynomialField hY h hK e he hframe _ hk b hb hΔ c d hc.contDiffOn hd.contDiffOn hy)]
  simp_rw [div_eq_mul_inv]
  rw [integral_mul_const]
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero (fun y hy => by
    rw [modeFischerDensity_zero_outside g e r k b c (fun ht => hy (hsuppc ht)),
      modeFischerDensity_zero_outside g e r k b d (fun ht => hy (hsuppd ht)), add_zero])]
  rw [integral_add (hp.integrable_modeFischerDensity hY h hK e he hfloor k b c hc hcompactc hsuppc)
    (hp.integrable_modeFischerDensity hY h hK e he hfloor k b d hd hcompactd hsuppd)]
  rw [hp.integral_modeFischerDensity hY h hK e he hfloor k b c hc hcompactc hsuppc,
    hp.integral_modeFischerDensity hY h hK e he hfloor k b d hd hcompactd hsuppd]

end ShrinkingSpheres
