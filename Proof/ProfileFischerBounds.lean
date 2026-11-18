import Proof.FischerIntegralBounds

noncomputable section
open Set MeasureTheory MvPolynomial
open scoped ContDiff
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.AngularPolynomial

lemma Profile.contDiffOn_beta {Y : Set X} (hY : IsOpen Y) {K : ℝ} {g : MetricField}
    (h : Elliptic Y K g) (hK : 0 < K) {e : Frame} {r : X → ℝ}
    {floor c₀ : ℝ} {Cj : Fin 9 → ℝ} (hp : Profile Y g e r floor c₀ Cj) (hfloor : 1 ≤ floor) :
    ContDiffOn ℝ ∞ (beta g r) Y := by
  have hf : ContDiffOn ℝ ∞ (fun x => Real.log (r x)) Y := hp.1.log (fun y hy => (hp.2 y hy).1.ne')
  have hd (i : I) : ContDiffOn ℝ ∞ (coordDeriv i (fun x => Real.log (r x))) Y :=
    (hf.fderiv_of_isOpen hY (by simp)).clm_apply contDiffOn_const
  have hS := ContDiffOn.sum (fun i (_ : i ∈ (Finset.univ : Finset I)) =>
    ContDiffOn.sum (fun j (_ : j ∈ (Finset.univ : Finset I)) =>
      ((h.contDiffOn_inverse_entry hK i j).mul (hd i)).mul (hd j)))
  apply hS.sqrt
  intro y hy
  have hβ : 0 < beta g r y := (lt_of_lt_of_le zero_lt_one hfloor).trans_le (hp.2 y hy).2.1
  exact (Real.sqrt_pos.mp hβ).ne'

variable {ι : Type*} [Fintype ι]

lemma Profile.fischerHessianForm_le {Y : Set X} (hY : IsOpen Y) {g : MetricField} {e : Frame} {r : X → ℝ}
    {floor c₀ : ℝ} {Cj : Fin 9 → ℝ} (hp : Profile Y g e r floor c₀ Cj)
    {y : X} (hy : y ∈ Y) (hframe : ∀ i j, metricPair g y (e y i) (e y j) = if i = j then 1 else 0)
    {k : ℕ} (b : ι → MvPolynomial I ℝ) (hb : ∀ a, (b a).IsHomogeneous k) (c : X → ι → ℝ) :
    fischerHessianForm g e b c (fun x => Real.log (r x)) k y ≤
      -2*c₀*(k : ℝ)^2*beta g r y*fischerInner (finitePolynomialField b c y) (finitePolynomialField b c y) := by
  have hf : ContDiffOn ℝ ∞ (fun x => Real.log (r x)) Y := hp.1.log (fun x hx => (hp.2 x hx).1.ne')
  have hdf := ((hf.fderiv_of_isOpen (m := ∞) hY (by simp)).contDiffAt (hY.mem_nhds hy)).differentiableAt (by simp)
  have hH (i j : I) : hessianBilinear g (fun x => Real.log (r x)) y (e y i) (e y j) =
      frameHessian g e (fun x => Real.log (r x)) y i j := hessianBilinear_eq_coordinate _ _ y hdf _ _
  unfold fischerHessianForm
  simp_rw [hH]
  exact hp.scaled_fischer_gradient_contraction hy hframe _ (finitePolynomialField_homogeneous b hb c y)

lemma Profile.integrable_beta_fischer {Y : Set X} (hY : IsOpen Y) {K : ℝ} {g : MetricField}
    (h : Elliptic Y K g) (hK : 0 < K) {e : Frame} {r : X → ℝ}
    {floor c₀ : ℝ} {Cj : Fin 9 → ℝ} (hp : Profile Y g e r floor c₀ Cj) (hfloor : 1 ≤ floor)
    (b : ι → MvPolynomial I ℝ) (c : X → ι → ℝ) (hc : ContDiffOn ℝ ∞ c Y)
    (hcompact : HasCompactSupport c) (hsupp : tsupport c ⊆ Y) :
    Integrable (fun y => metricDensity g y * beta g r y *
      fischerInner (finitePolynomialField b c y) (finitePolynomialField b c y)) :=
  integrable_weighted_fischerPair_local hY _ ((h.contDiffOn_density hK).mul (hp.contDiffOn_beta hY h hK hfloor))
    b b c c hc hc hcompact hsupp

theorem Profile.loweredHessianEnergy_le {Y : Set X} (hY : IsOpen Y) {K : ℝ} {g : MetricField}
    (h : Elliptic Y K g) (hK : 0 < K) (e : Frame)
    (he : ∀ i, ContDiffOn ℝ ∞ (fun x => e x i) Y)
    (hframe : ∀ x ∈ Y, ∀ i j, metricPair g x (e x i) (e x j) = if i = j then 1 else 0)
    {r : X → ℝ} {floor c₀ : ℝ} {Cj : Fin 9 → ℝ} (hp : Profile Y g e r floor c₀ Cj) (hfloor : 1 ≤ floor)
    {k : ℕ} (b : ι → MvPolynomial I ℝ) (hb : ∀ a, (b a).IsHomogeneous k)
    (c : X → ι → ℝ) (hc : ContDiffOn ℝ ∞ c Y) (hcompact : HasCompactSupport c) (hsupp : tsupport c ⊆ Y) :
    loweredHessianEnergy g e b c (fun x => Real.log (r x)) k ≤
      (-2*c₀*(k : ℝ)^2)*(∫ y, metricDensity g y * beta g r y *
        fischerInner (finitePolynomialField b c y) (finitePolynomialField b c y)) := by
  have hf : ContDiffOn ℝ ∞ (fun x => Real.log (r x)) Y := hp.1.log (fun x hx => (hp.2 x hx).1.ne')
  have hH := integrable_fischerHessianForm hY h hK e he b c _ k hc hf hcompact hsupp
  have hM := hp.integrable_beta_fischer hY h hK hfloor b c hc hcompact hsupp
  have hpoint (y : X) : metricDensity g y * fischerHessianForm g e b c (fun x => Real.log (r x)) k y ≤
      (-2*c₀*(k : ℝ)^2)*(metricDensity g y * beta g r y *
        fischerInner (finitePolynomialField b c y) (finitePolynomialField b c y)) := by
    by_cases hy : y ∈ Y
    · have hh := mul_le_mul_of_nonneg_left (hp.fischerHessianForm_le hY hy (hframe y hy) b hb c)
        (show 0 ≤ metricDensity g y from Real.sqrt_nonneg _)
      exact hh.trans_eq (by ring)
    · have hout : y ∉ tsupport c := fun ht => hy (hsupp ht)
      simp [fischerHessianForm, finitePolynomialField_zero_outside b c hout, fischerInner_zero_left]
  calc
    _ ≤ ∫ y, (-2*c₀*(k : ℝ)^2)*(metricDensity g y * beta g r y *
        fischerInner (finitePolynomialField b c y) (finitePolynomialField b c y)) :=
      integral_mono hH (hM.const_mul _) hpoint
    _ = _ := integral_const_mul _ _

lemma Profile.floor_fischer_mass_le {Y : Set X} (hY : IsOpen Y) {K : ℝ} {g : MetricField}
    (h : Elliptic Y K g) (hK : 0 < K) {e : Frame} {r : X → ℝ}
    {floor c₀ : ℝ} {Cj : Fin 9 → ℝ} (hp : Profile Y g e r floor c₀ Cj) (hfloor : 1 ≤ floor)
    (b : ι → MvPolynomial I ℝ) (c : X → ι → ℝ) (hc : ContDiffOn ℝ ∞ c Y)
    (hcompact : HasCompactSupport c) (hsupp : tsupport c ⊆ Y) :
    floor*(∫ y, metricDensity g y * fischerInner (finitePolynomialField b c y) (finitePolynomialField b c y)) ≤
      ∫ y, metricDensity g y * beta g r y * fischerInner (finitePolynomialField b c y) (finitePolynomialField b c y) := by
  have hU := integrable_weighted_fischerPair_local hY (metricDensity g) (h.contDiffOn_density hK) b b c c hc hc hcompact hsupp
  have hM := hp.integrable_beta_fischer hY h hK hfloor b c hc hcompact hsupp
  rw [← integral_const_mul]
  apply integral_mono (hU.const_mul _) hM
  intro y
  by_cases hy : y ∈ Y
  · have hh := mul_le_mul_of_nonneg_right (hp.2 y hy).2.1
      (mul_nonneg (show 0 ≤ metricDensity g y from Real.sqrt_nonneg _) (fischerInner_self_nonneg (finitePolynomialField b c y)))
    nlinarith only [hh]
  · have hout : y ∉ tsupport c := fun ht => hy (hsupp ht)
    simp [finitePolynomialField_zero_outside b c hout, fischerInner_zero_left]

/-- A sufficiently large profile slope absorbs the full curvature error, uniformly in the
    homogeneous degree. The bound uses the actual curvature coefficients and arbitrary radius. -/
theorem Profile.crossEnergy_lower_bound {Y : Set X} (hY : IsOpen Y) {K : ℝ} {g : MetricField}
    (h : Elliptic Y K g) (hK : 0 < K) (e : Frame)
    (he : ∀ i, ContDiffOn ℝ ∞ (fun x => e x i) Y)
    (hframe : ∀ x ∈ Y, ∀ i j, metricPair g x (e x i) (e x j) = if i = j then 1 else 0)
    {r : X → ℝ} {floor c₀ : ℝ} {Cj : Fin 9 → ℝ} (hp : Profile Y g e r floor c₀ Cj)
    (hc₀ : 0 < c₀) (hfloor : 1 ≤ floor) (B : ℝ) (hB : 0 ≤ B)
    (hR : ∀ y ∈ Y, ∀ i j a b, |frameCurvatureCoefficient g e y (e y i) (e y j) a b| ≤ B)
    (hthreshold : 9*B ≤ c₀*floor) {k : ℕ} (hk : 1 ≤ k)
    (b : ι → MvPolynomial I ℝ) (hb : ∀ a, (b a).IsHomogeneous k)
    (c : X → ι → ℝ) (hc : ContDiff ℝ ∞ c) (hcompact : HasCompactSupport c) (hsupp : tsupport c ⊆ Y) :
    loweredWeightedTraceSquare g e b c (fun x => Real.log (r x)) k (-1) +
      c₀*(k : ℝ)^2*(∫ y, metricDensity g y * beta g r y *
        fischerInner (finitePolynomialField b c y) (finitePolynomialField b c y)) ≤
      loweredWeightedCrossEnergy g e b c (fun x => Real.log (r x)) k 1 := by
  let U : ℝ := ∫ y, metricDensity g y * fischerInner (finitePolynomialField b c y) (finitePolynomialField b c y)
  let M : ℝ := ∫ y, metricDensity g y * beta g r y *
    fischerInner (finitePolynomialField b c y) (finitePolynomialField b c y)
  have hU : 0 ≤ U := integral_nonneg (fun y => mul_nonneg (Real.sqrt_nonneg _) (fischerInner_self_nonneg _))
  have hFM : floor*U ≤ M := hp.floor_fischer_mass_le hY h hK hfloor b c hc.contDiffOn hcompact hsupp
  have hbudget : 9*B*U ≤ c₀*M := by
    calc
      _ ≤ (c₀*floor)*U := mul_le_mul_of_nonneg_right hthreshold hU
      _ = c₀*(floor*U) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hFM hc₀.le
  have hE := integratedFullCovectorCurvature_bound hY h hK e he hframe B hB hR hk b hb c hc.contDiffOn hcompact hsupp
  have hE' : |integratedFullCovectorCurvature g e b c| ≤ c₀*(k : ℝ)^2*M := by
    refine hE.trans ?_
    have hh := mul_le_mul_of_nonneg_left hbudget (sq_nonneg (k : ℝ))
    convert hh using 1 <;> ring
  have hH := hp.loweredHessianEnergy_le hY h hK e he hframe hfloor b hb c hc.contDiffOn hcompact hsupp
  have hf : ContDiffOn ℝ ∞ (fun x => Real.log (r x)) Y := hp.1.log (fun x hx => (hp.2 x hx).1.ne')
  rw [loweredWeighted_first_integrated_identity hY h hK e he hframe b c _ k hc hf hcompact hsupp]
  change _ + c₀*(k : ℝ)^2*M ≤ _
  have hlo := (abs_le.mp hE').1
  change loweredHessianEnergy g e b c (fun x => Real.log (r x)) k ≤ (-2*c₀*(k : ℝ)^2)*M at hH
  nlinarith only [hlo, hH]

end ShrinkingSpheres
