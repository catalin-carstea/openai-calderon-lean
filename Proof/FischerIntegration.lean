import Proof.FischerFields
import Proof.FrameDuality
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts

noncomputable section
open Set MeasureTheory MvPolynomial
open scoped ContDiff
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.AngularPolynomial

/-- Coordinate divergence of a vector field with its integration density included. -/
def weightedDivergence (ρ : X → ℝ) (V : X → X) (y : X) : ℝ :=
  ∑ i, coordDeriv i (fun x => ρ x * V x i) y

lemma contDiff_coordDeriv (i : I) (P : X → ℝ) (hP : ContDiff ℝ ∞ P) :
    ContDiff ℝ ∞ (coordDeriv i P) :=
  (hP.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const

/-- The scalar variable-vector-field integration by parts used in the supplied density proof. -/
theorem compact_scalar_variable_adjoint (ρ P : X → ℝ) (V : X → X)
    (hρ : ContDiff ℝ ∞ ρ) (hP : ContDiff ℝ ∞ P) (hV : ContDiff ℝ ∞ V)
    (hc : HasCompactSupport P) :
    (∫ y, ρ y * fderiv ℝ P y (V y)) = -(∫ y, weightedDivergence ρ V y * P y) := by
  have hVi (i : I) : ContDiff ℝ ∞ (fun x => V x i) := (EuclideanSpace.proj (𝕜 := ℝ) i).contDiff.comp hV
  have hi (i : I) : Integrable (fun y => ρ y * V y i * coordDeriv i P y) :=
    (((hρ.mul (hVi i)).continuous).mul (contDiff_coordDeriv i P hP).continuous).integrable_of_hasCompactSupport
      (hc.fderiv_apply (𝕜 := ℝ) (axis i)).mul_left
  have hj (i : I) : Integrable (fun y => coordDeriv i (fun x => ρ x * V x i) y * P y) :=
    ((contDiff_coordDeriv i _ (hρ.mul (hVi i))).continuous.mul hP.continuous).integrable_of_hasCompactSupport hc.mul_left
  have hzero (i : I) : Integrable (fun y => (ρ y * V y i) * P y) :=
    ((hρ.mul (hVi i)).continuous.mul hP.continuous).integrable_of_hasCompactSupport hc.mul_left
  have hfun : (fun y => ρ y * fderiv ℝ P y (V y)) =
      (fun y => ∑ i, ρ y * V y i * coordDeriv i P y) := by
    funext y
    rw [linear_axis_expansion, Finset.mul_sum]
    simp only [coordDeriv, mul_assoc]
  rw [hfun, show (fun y => weightedDivergence ρ V y * P y) =
    (fun y => ∑ i, coordDeriv i (fun x => ρ x * V x i) y * P y) by
      funext y; simp only [weightedDivergence, Finset.sum_mul]]
  rw [integral_finsetSum _ (fun i _ => hi i), integral_finsetSum _ (fun i _ => hj i),
    ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro i _
  exact integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
    (μ := (volume : Measure X)) (f := fun y => ρ y * V y i) (g := P) (v := axis i)
    (hj i) (hi i) (hzero i)
    (fun y _ => (hρ.mul (hVi i)).differentiable (by simp) y)
    (fun y _ => hP.differentiable (by simp) y)

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

lemma contDiff_fischerPair (b : ι → MvPolynomial I ℝ) (d : κ → MvPolynomial I ℝ)
    (c : X → ι → ℝ) (z : X → κ → ℝ) (hc : ContDiff ℝ ∞ c) (hz : ContDiff ℝ ∞ z) :
    ContDiff ℝ ∞ (fun x => fischerInner (finitePolynomialField b c x) (finitePolynomialField d z x)) := by
  have hfun : (fun x => fischerInner (finitePolynomialField b c x) (finitePolynomialField d z x)) =
      (fun x => polynomialFamilyFischerBilinear b d (c x) (z x)) := by
    funext x
    rw [fischerInner_finitePolynomialField, polynomialFamilyFischerBilinear_apply]
  rw [hfun]
  exact ((polynomialFamilyFischerBilinear b d).contDiff.comp hc).clm_apply hz

lemma hasCompactSupport_fischerPair (b : ι → MvPolynomial I ℝ) (d : κ → MvPolynomial I ℝ)
    (c : X → ι → ℝ) (z : X → κ → ℝ) (hc : HasCompactSupport c) :
    HasCompactSupport (fun x => fischerInner (finitePolynomialField b c x) (finitePolynomialField d z x)) := by
  apply hc.mono
  intro x hx
  simp only [Function.mem_support] at hx ⊢
  contrapose! hx
  simp only [fischerInner_finitePolynomialField, hx, Pi.zero_apply, zero_mul, Finset.sum_const_zero]

/-- The derivative pairing remains valid globally when one coefficient field is supported
    in the region on which the geometry is smooth. -/
lemma covariant_fischer_pair_derivative {Ω : Set X} (hΩ : IsOpen Ω) {K : ℝ}
    {g : MetricField} (h : Elliptic Ω K g) (hK : 0 < K) (e : Frame)
    (he : ∀ i, ContDiffOn ℝ ∞ (fun x => e x i) Ω)
    (hframe : ∀ x ∈ Ω, ∀ i j, metricPair g x (e x i) (e x j) = if i = j then 1 else 0)
    (b : ι → MvPolynomial I ℝ) (d : κ → MvPolynomial I ℝ)
    (c : X → ι → ℝ) (z : X → κ → ℝ) (hc : ContDiff ℝ ∞ c) (hz : ContDiff ℝ ∞ z)
    (hsupp : tsupport c ⊆ Ω) (y a : X) :
    fderiv ℝ (fun x => fischerInner (finitePolynomialField b c x) (finitePolynomialField d z x)) y a =
      fischerInner (covariantPolynomialDerivative g e b c y a) (finitePolynomialField d z y) +
        fischerInner (finitePolynomialField b c y) (covariantPolynomialDerivative g e d z y a) := by
  by_cases hy : y ∈ Ω
  · exact covariantPolynomialDerivative_fischer_compatible hΩ h hK e he hframe b d c z hy a
      (hc.differentiable (by simp) y) (hz.differentiable (by simp) y)
  · have hout : y ∉ tsupport c := fun hyc => hy (hsupp hyc)
    have hc0 := image_eq_zero_of_notMem_tsupport hout
    have hdc0 := fderiv_of_notMem_tsupport (𝕜 := ℝ) hout
    rw [fderiv_fischerInner_finitePolynomialField b d c z y a
      (hc.differentiable (by simp) y) (hz.differentiable (by simp) y)]
    simp [covariantPolynomialDerivative, finitePolynomialField, finitePolynomialFieldDerivative,
      hc0, hdc0, polynomialConnectionAction, fischerInner_zero_left, fischerInner_zero_right]

/-- Covariant integration by parts uses geometry only on Ω. Compact support keeps the
    polynomial field away from its boundary, so arbitrary exterior extensions do not enter. -/
theorem compact_covariant_fischer_contraction {Ω : Set X} (hΩ : IsOpen Ω) {K : ℝ}
    {g : MetricField} (h : Elliptic Ω K g) (hK : 0 < K) (e : Frame)
    (he : ∀ i, ContDiffOn ℝ ∞ (fun x => e x i) Ω)
    (hframe : ∀ x ∈ Ω, ∀ i j, metricPair g x (e x i) (e x j) = if i = j then 1 else 0)
    (ρ : X → ℝ) (hρ : ContDiff ℝ ∞ ρ) (V : X → X) (hV : ContDiff ℝ ∞ V)
    (b : ι → MvPolynomial I ℝ) (d : κ → MvPolynomial I ℝ)
    (c : X → ι → ℝ) (z : X → κ → ℝ) (hc : ContDiff ℝ ∞ c) (hz : ContDiff ℝ ∞ z)
    (hcompact : HasCompactSupport c) (hsupp : tsupport c ⊆ Ω) :
    (∫ y, ρ y * (fischerInner (covariantPolynomialDerivative g e b c y (V y)) (finitePolynomialField d z y) +
      fischerInner (finitePolynomialField b c y) (covariantPolynomialDerivative g e d z y (V y)))) =
      -(∫ y, weightedDivergence ρ V y * fischerInner (finitePolynomialField b c y) (finitePolynomialField d z y)) := by
  have hpoint (y : X) := covariant_fischer_pair_derivative hΩ h hK e he hframe b d c z hc hz hsupp y (V y)
  have hh := compact_scalar_variable_adjoint ρ
    (fun x => fischerInner (finitePolynomialField b c x) (finitePolynomialField d z x)) V hρ
    (contDiff_fischerPair b d c z hc hz) hV (hasCompactSupport_fischerPair b d c z hcompact)
  simpa only [hpoint] using hh

end ShrinkingSpheres
