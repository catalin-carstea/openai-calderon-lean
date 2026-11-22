module

public import Proof.CalderonN.FiberFischer
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Tactic

@[expose] public section

/- Port of SphereModeEnergy.lean from the checked Proposition 5.3 release f308cb9d. -/
noncomputable section
open Set Filter MeasureTheory MvPolynomial
open scoped ContDiff Topology
namespace CalderonN
variable {n : ℕ}

variable [NeZero n]

open OAI.AnisotropicCalderon.AngularPolynomial

/-- The four degree-k energy terms, evaluated with the contract's actual sphere measure.
    Identifying this with the Sobolev energy still requires the Legendre projection theorem. -/
def sphereModeDensity (g : (MetricField n)) (e : (Frame n)) (r : (X n) → ℝ) (k : ℕ) (φ : (Field n)) (y : (X n)) : ℝ :=
  let H := ∑ i, fiberSq e y (fun w => horizontal g φ y w (e y i))
  let V := fiberSq e y (fun w => φ (y,w))
  metricDensity g y * (H + (1+(k : ℝ))^2*(beta g r y)^2*V +
    (1+(k : ℝ))*(beta g r y)⁻¹*H + (1+(k : ℝ))^3*beta g r y*V)

def sphereModeEnergy (Y : Set (X n)) (g : (MetricField n)) (e : (Frame n)) (r : (X n) → ℝ) (k : ℕ) (φ : (Field n)) : ℝ :=
  ∫ y in Y, sphereModeDensity g e r k φ y

variable {ι : Type*} [Fintype ι]

def modeFischerDensity (g : (MetricField n)) (e : (Frame n)) (r : (X n) → ℝ) (k : ℕ)
    (b : ι → MvPolynomial (I n) ℝ) (c : (X n) → ι → ℝ) (y : (X n)) : ℝ :=
  let F := fischerInner (finitePolynomialField b c y) (finitePolynomialField b c y)
  let H := covariantFrameEnergy g e b c y
  metricDensity g y * (H + (1+(k : ℝ))^2*(beta g r y)^2*F +
    (1+(k : ℝ))*(beta g r y)⁻¹*H + (1+(k : ℝ))^3*beta g r y*F)

lemma modeFischerDensity_zero_outside (g : (MetricField n)) (e : (Frame n)) (r : (X n) → ℝ) (k : ℕ)
    (b : ι → MvPolynomial (I n) ℝ) (c : (X n) → ι → ℝ) {y : (X n)} (hy : y ∉ tsupport c) :
    modeFischerDensity g e r k b c y = 0 := by
  simp [modeFischerDensity, covariantFrameEnergy, finitePolynomialField_zero_outside b c hy,
    covariantPolynomialDerivative_zero_outside g e b c hy, fischerInner_zero_left]

theorem sphereModeDensity_complexPolynomialField {Y : Set (X n)} (hY : IsOpen Y) {K : ℝ} {g : (MetricField n)}
    (h : Elliptic Y K g) (hK : 0 < K) (e : (Frame n))
    (he : ∀ i, ContDiffOn ℝ ∞ (fun x => e x i) Y)
    (hframe : ∀ y ∈ Y, ∀ i j, metricPair g y (e y i) (e y j) = if i = j then 1 else 0)
    (r : (X n) → ℝ) {k : ℕ} (hk : 1 ≤ k) (b : ι → MvPolynomial (I n) ℝ)
    (hb : ∀ a, (b a).IsHomogeneous k) (hΔ : ∀ a, laplacian (b a) = 0)
    (c : (X n) → ι → ℝ) (hc : ContDiffOn ℝ ∞ c Y) {y : (X n)} (hy : y ∈ Y) :
    sphereModeDensity g e r k (complexPolynomialField g e b c) y =
      modeFischerDensity g e r k b c y / sphereNormalization n k := by
  have hV := fiberSq_complexPolynomialField g e y (hframe y hy) b hb hΔ c
  have hH : (∑ i, fiberSq e y (fun w => horizontal g (complexPolynomialField g e b c) y w (e y i))) =
      covariantFrameEnergy g e b c y / sphereNormalization n k := by
    simp_rw [fiberSq_complexPolynomialField_horizontal hY h hK e he hframe hk b hb hΔ c hc hy]
    simp only [normalizedFischerSquare, normalizedFischerInner, Fintype.card_fin,
      ← Finset.sum_div, covariantFrameEnergy]
  simp only [sphereModeDensity, hV, hH, normalizedFischerSquare, normalizedFischerInner,
    Fintype.card_fin, modeFischerDensity]
  ring

lemma Profile.integral_modeFischerDensity {Y : Set (X n)} (hY : IsOpen Y) {K : ℝ} {g : (MetricField n)}
    (h : Elliptic Y K g) (hK : 0 < K) (e : (Frame n))
    (he : ∀ i, ContDiffOn ℝ ∞ (fun x => e x i) Y)
    {r : (X n) → ℝ} {floor c₀ : ℝ} {Cj : Fin 9 → ℝ} (hp : Profile Y g e r floor c₀ Cj) (hfloor : 1 ≤ floor)
    (k : ℕ) (b : ι → MvPolynomial (I n) ℝ) (c : (X n) → ι → ℝ) (hc : ContDiff ℝ ∞ c)
    (hcompact : HasCompactSupport c) (hsupp : tsupport c ⊆ Y) :
    (∫ y, modeFischerDensity g e r k b c y) = profileModeFischerEnergy g e r k b c := by
  let D := fun y => metricDensity g y * covariantFrameEnergy g e b c y
  let V := fun y => metricDensity g y * (beta g r y)^2 * fischerInner (finitePolynomialField b c y) (finitePolynomialField b c y)
  let Iw := fun y => metricDensity g y * (beta g r y)⁻¹ * covariantFrameEnergy g e b c y
  let M := fun y => metricDensity g y * beta g r y * fischerInner (finitePolynomialField b c y) (finitePolynomialField b c y)
  let weight : ℝ := 1+k
  have hD : Integrable D := (integrable_frameEnergyTerms hY h hK e he _ (h.contDiffOn_density hK)
    (fun _ => 0) contDiffOn_const b c hc hcompact hsupp).1
  have hV : Integrable V := integrable_weighted_fischerPair_local hY _
    ((h.contDiffOn_density hK).mul ((hp.contDiffOn_beta hY h hK hfloor).pow 2)) b b c c
    hc.contDiffOn hc.contDiffOn hcompact hsupp
  have hI : Integrable Iw := by
    simpa only [weightedFrameEnergy_zero] using hp.integrable_inv_frameEnergy hY h hK e he hfloor b c 0 1 hc hcompact hsupp
  have hM : Integrable M := hp.integrable_beta_fischer hY h hK hfloor b c hc.contDiffOn hcompact hsupp
  have hfun : modeFischerDensity g e r k b c = fun y => D y+weight^2*V y+weight*Iw y+weight^3*M y := by
    funext y
    dsimp only [modeFischerDensity, D, V, Iw, M, weight]
    ring
  have hsplit1 := integral_add ((hD.add (hV.const_mul (weight^2))).add (hI.const_mul weight)) (hM.const_mul (weight^3))
  have hsplit2 := integral_add (hD.add (hV.const_mul (weight^2))) (hI.const_mul weight)
  have hsplit3 := integral_add hD (hV.const_mul (weight^2))
  simp only [Pi.add_apply] at hsplit1 hsplit2 hsplit3
  rw [hfun, hsplit1, hsplit2, hsplit3]
  simp only [integral_const_mul, profileModeFischerEnergy, profileSecondMass,
    profileWeightedFrameEnergy, profileFischerMass, weightedFrameEnergy_zero]
  rfl

/-- The finite mode energy is an actual integral over Y with the frozen sphere probability
    measure. The coefficients vanish off a compact subset of Y. -/
theorem Profile.sphereModeEnergy_eq_fischer {Y : Set (X n)} (hY : IsOpen Y) {K : ℝ} {g : (MetricField n)}
    (h : Elliptic Y K g) (hK : 0 < K) (e : (Frame n))
    (he : ∀ i, ContDiffOn ℝ ∞ (fun x => e x i) Y)
    (hframe : ∀ y ∈ Y, ∀ i j, metricPair g y (e y i) (e y j) = if i = j then 1 else 0)
    {r : (X n) → ℝ} {floor c₀ : ℝ} {Cj : Fin 9 → ℝ} (hp : Profile Y g e r floor c₀ Cj) (hfloor : 1 ≤ floor)
    {k : ℕ} (hk : 1 ≤ k) (b : ι → MvPolynomial (I n) ℝ)
    (hb : ∀ a, (b a).IsHomogeneous k) (hΔ : ∀ a, laplacian (b a) = 0)
    (c : (X n) → ι → ℝ) (hc : ContDiff ℝ ∞ c) (hcompact : HasCompactSupport c) (hsupp : tsupport c ⊆ Y) :
    sphereModeEnergy Y g e r k (complexPolynomialField g e b c) =
      profileModeFischerEnergy g e r k b c / sphereNormalization n k := by
  unfold sphereModeEnergy
  rw [setIntegral_congr_fun hY.measurableSet (fun y hy =>
    sphereModeDensity_complexPolynomialField hY h hK e he hframe r hk b hb hΔ c hc.contDiffOn hy)]
  simp_rw [div_eq_mul_inv]
  rw [integral_mul_const]
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero (fun y hy =>
    modeFischerDensity_zero_outside g e r k b c (fun ht => hy (hsupp ht)))]
  rw [hp.integral_modeFischerDensity hY h hK e he hfloor k b c hc hcompact hsupp]

end CalderonN
