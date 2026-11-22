module

public import Proof.CalderonN.FiniteProfileGain
import Mathlib.Tactic

@[expose] public section

/- Port of ProfileModeEnergy.lean from the checked Proposition 5.3 release f308cb9d. -/
noncomputable section
open Set Filter MeasureTheory MvPolynomial
open scoped ContDiff Topology
namespace CalderonN
variable {n : ℕ}

variable [NeZero n]

open OAI.AnisotropicCalderon.AngularPolynomial

variable {ι : Type*} [Fintype ι]

def profileSecondMass (g : (MetricField n)) (b : ι → MvPolynomial (I n) ℝ) (c : (X n) → ι → ℝ) (r : (X n) → ℝ) : ℝ :=
  ∫ y, metricDensity g y * (beta g r y)^2 * fischerInner (finitePolynomialField b c y) (finitePolynomialField b c y)

def profileModeFischerEnergy (g : (MetricField n)) (e : (Frame n)) (r : (X n) → ℝ) (k : ℕ)
    (b : ι → MvPolynomial (I n) ℝ) (c : (X n) → ι → ℝ) : ℝ :=
  (∫ y, metricDensity g y * covariantFrameEnergy g e b c y) +
    (1+(k : ℝ))^2*profileSecondMass g b c r +
    (1+(k : ℝ))*profileWeightedFrameEnergy g e b c r 0 1 +
    (1+(k : ℝ))^3*profileFischerMass g b c r

lemma profileSecondMass_nonneg (g : (MetricField n)) (b : ι → MvPolynomial (I n) ℝ) (c : (X n) → ι → ℝ) (r : (X n) → ℝ) :
    0 ≤ profileSecondMass g b c r :=
  integral_nonneg (fun y => mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) (sq_nonneg _)) (fischerInner_self_nonneg _))

lemma weightedFrameEnergy_zero (g : (MetricField n)) (e : (Frame n)) (b : ι → MvPolynomial (I n) ℝ)
    (c : (X n) → ι → ℝ) (f : (X n) → ℝ) (y : (X n)) : weightedFrameEnergy g e b c f 0 1 y = covariantFrameEnergy g e b c y := by
  simp [weightedFrameEnergy, weightedPolynomialDerivative, covariantFrameEnergy]

lemma weightedFrameEnergy_gradient_bound (g : (MetricField n)) (e : (Frame n))
    (b : ι → MvPolynomial (I n) ℝ) (c : (X n) → ι → ℝ) (f : (X n) → ℝ) (k : ℝ) (y : (X n)) :
    covariantFrameEnergy g e b c y ≤ 2*weightedFrameEnergy g e b c f k 1 y +
      2*k^2*frameGradientSq e f y*fischerInner (finitePolynomialField b c y) (finitePolynomialField b c y) := by
  have hi (i : (I n)) : fischerInner (covariantPolynomialDerivative g e b c y (e y i))
      (covariantPolynomialDerivative g e b c y (e y i)) ≤
      2*fischerInner (weightedPolynomialDerivative g e b c f k 1 y (e y i))
        (weightedPolynomialDerivative g e b c f k 1 y (e y i)) +
      2*k^2*(fderiv ℝ f y (e y i))^2*fischerInner (finitePolynomialField b c y) (finitePolynomialField b c y) := by
    let q := weightedPolynomialDerivative g e b c f k 1 y (e y i)
    let w := k*fderiv ℝ f y (e y i)
    have hrel : q+C (-w)*finitePolynomialField b c y = covariantPolynomialDerivative g e b c y (e y i) := by
      simp only [q, w, weightedPolynomialDerivative, map_one, one_mul, map_neg]
      ring
    have hh := fischerInner_self_add_le q (C (-w)*finitePolynomialField b c y)
    rw [hrel] at hh
    simp only [fischerInner_C_mul_left, fischerInner_C_mul_right] at hh
    apply hh.trans_eq
    dsimp only [q, w]
    ring
  have hh := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hi i)
  apply hh.trans_eq
  simp only [covariantFrameEnergy, weightedFrameEnergy, frameGradientSq, Finset.sum_add_distrib,
    Finset.mul_sum, Finset.sum_mul]

theorem Profile.weightedFrameEnergy_controls_gradient {Y : Set (X n)} (hY : IsOpen Y) {K : ℝ} {g : (MetricField n)}
    (h : Elliptic Y K g) (hK : 0 < K) (e : (Frame n))
    (he : ∀ i, ContDiffOn ℝ ∞ (fun x => e x i) Y)
    (hframe : ∀ y ∈ Y, ∀ i j, metricPair g y (e y i) (e y j) = if i = j then 1 else 0)
    {r : (X n) → ℝ} {floor c₀ : ℝ} {Cj : Fin 9 → ℝ} (hp : Profile Y g e r floor c₀ Cj) (hfloor : 1 ≤ floor)
    (b : ι → MvPolynomial (I n) ℝ) (c : (X n) → ι → ℝ) (hc : ContDiff ℝ ∞ c)
    (hcompact : HasCompactSupport c) (hsupp : tsupport c ⊆ Y) (k : ℝ) :
    profileWeightedFrameEnergy g e b c r 0 1 ≤
      2*profileWeightedFrameEnergy g e b c r k 1 + 2*k^2*profileFischerMass g b c r := by
  let f := fun x => Real.log (r x)
  have hG := hp.integrable_inv_frameEnergy hY h hK e he hfloor b c 0 1 hc hcompact hsupp
  have hW := hp.integrable_inv_frameEnergy hY h hK e he hfloor b c k 1 hc hcompact hsupp
  have hM := hp.integrable_beta_fischer hY h hK hfloor b c hc.contDiffOn hcompact hsupp
  have hh : profileWeightedFrameEnergy g e b c r 0 1 ≤
      ∫ y, 2*(metricDensity g y*(beta g r y)⁻¹*weightedFrameEnergy g e b c f k 1 y) +
        (2*k^2)*(metricDensity g y*beta g r y*fischerInner (finitePolynomialField b c y) (finitePolynomialField b c y)) := by
    apply integral_mono hG ((hW.const_mul _).add (hM.const_mul _))
    intro y
    change metricDensity g y*(beta g r y)⁻¹*weightedFrameEnergy g e b c f 0 1 y ≤
      2*(metricDensity g y*(beta g r y)⁻¹*weightedFrameEnergy g e b c f k 1 y) +
      (2*k^2)*(metricDensity g y*beta g r y*fischerInner (finitePolynomialField b c y) (finitePolynomialField b c y))
    by_cases hy : y ∈ Y
    · have hβ : 0 < beta g r y := (lt_of_lt_of_le zero_lt_one hfloor).trans_le (hp.2 y hy).2.1
      have hpoint := mul_le_mul_of_nonneg_left (weightedFrameEnergy_gradient_bound g e b c f k y)
        (show 0 ≤ metricDensity g y*(beta g r y)⁻¹ from mul_nonneg (Real.sqrt_nonneg _) (inv_nonneg.mpr hβ.le))
      rw [weightedFrameEnergy_zero]
      apply hpoint.trans_eq
      have hsq : frameGradientSq e f y = (beta g r y)^2 := (beta_sq g e r y (hframe y hy)).symm
      rw [hsq]
      field_simp [hβ.ne'] <;> ring
    · have hout : y ∉ tsupport c := fun ht => hy (hsupp ht)
      simp [weightedFrameEnergy_zero_outside g e b c _ 0 1 hout,
        weightedFrameEnergy_zero_outside g e b c f k 1 hout, finitePolynomialField_zero_outside b c hout, fischerInner_zero_left]
  apply hh.trans_eq
  rw [integral_add (hW.const_mul _) (hM.const_mul _)]
  simp only [integral_const_mul, profileWeightedFrameEnergy, profileFischerMass]

theorem Profile.modeFischerEnergy_le {Y : Set (X n)} (hY : IsOpen Y) {K : ℝ} {g : (MetricField n)}
    (h : Elliptic Y K g) (hK : 0 < K) (e : (Frame n))
    (he : ∀ i, ContDiffOn ℝ ∞ (fun x => e x i) Y)
    (hframe : ∀ y ∈ Y, ∀ i j, metricPair g y (e y i) (e y j) = if i = j then 1 else 0)
    {r : (X n) → ℝ} {floor c₀ : ℝ} {Cj : Fin 9 → ℝ} (hp : Profile Y g e r floor c₀ Cj)
    (hc₀ : 0 < c₀) (hfloor : 1 ≤ floor) {k : ℕ} (hk : 1 ≤ k)
    (b : ι → MvPolynomial (I n) ℝ) (c : (X n) → ι → ℝ) (hc : ContDiff ℝ ∞ c)
    (hcompact : HasCompactSupport c) (hsupp : tsupport c ⊆ Y) :
    profileModeFischerEnergy g e r k b c ≤
      4*(∫ y, metricDensity g y * weightedFrameEnergy g e b c (fun x => Real.log (r x)) k 1 y) +
      4*(k : ℝ)*profileWeightedFrameEnergy g e b c r k 1 + 12*(k : ℝ)^3*profileFischerMass g b c r := by
  let degree : ℝ := k
  let D := ∫ y, metricDensity g y * covariantFrameEnergy g e b c y
  let V := profileSecondMass g b c r
  let Iw := profileWeightedFrameEnergy g e b c r 0 1
  let M := profileFischerMass g b c r
  let Eplus := ∫ y, metricDensity g y * weightedFrameEnergy g e b c (fun x => Real.log (r x)) k 1 y
  let W := profileWeightedFrameEnergy g e b c r k 1
  have hn : 1 ≤ degree := by change (1 : ℝ) ≤ (k : ℝ); exact_mod_cast hk
  have hn0 : 0 ≤ degree := by linarith
  have hD : 0 ≤ D := integral_nonneg (fun y => mul_nonneg (Real.sqrt_nonneg _) (Finset.sum_nonneg (fun i _ => fischerInner_self_nonneg _)))
  have hV : 0 ≤ V := profileSecondMass_nonneg g b c r
  have hIw : 0 ≤ Iw := profileWeightedFrameEnergy_nonneg g e b c r 0 1
  have hM : 0 ≤ M := profileFischerMass_nonneg g b c r
  have hplain : D+degree^2*V ≤ Eplus := profile_weighted_energy_bound hY h hK e he hframe hp hc₀ hfloor b c hc hcompact hsupp hn0
  have hweight : Iw ≤ 2*W+2*degree^2*M := hp.weightedFrameEnergy_controls_gradient hY h hK e he hframe hfloor b c hc hcompact hsupp k
  have hfac : 1+degree ≤ 2*degree := by linarith
  have hfac2 : (1+degree)^2 ≤ 4*degree^2 := by nlinarith
  have hpart1 : D+(1+degree)^2*V ≤ 4*Eplus := by
    have hh := mul_le_mul_of_nonneg_right hfac2 hV
    linarith only [hh, hplain, hD]
  have hpart2 : (1+degree)*Iw ≤ 4*degree*W+4*degree^3*M := by
    have hh := mul_le_mul_of_nonneg_right hfac hIw
    have hw := mul_le_mul_of_nonneg_left hweight (show 0 ≤ 2*degree by positivity)
    nlinarith only [hh, hw]
  have hpart3 : (1+degree)^3*M ≤ 8*degree^3*M := by
    calc
      _ ≤ (2*degree)^3*M := by gcongr
      _ = _ := by ring
  change D+(1+degree)^2*V+(1+degree)*Iw+(1+degree)^3*M ≤ 4*Eplus+4*degree*W+12*degree^3*M
  linarith

end CalderonN
