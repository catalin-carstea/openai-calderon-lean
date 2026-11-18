import Proof.Localization
import Proof.MetricDensity

noncomputable section
open Set MeasureTheory MvPolynomial
open scoped ContDiff
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.AngularPolynomial

lemma weightedDivergence_congr {ρ σ : X → ℝ} {V W : X → X} {y : X}
    (hρ : ρ =ᶠ[nhds y] σ) (hV : V =ᶠ[nhds y] W) :
    weightedDivergence ρ V y = weightedDivergence σ W y := by
  apply Finset.sum_congr rfl
  intro i _
  have heq : (fun x => ρ x * V x i) =ᶠ[nhds y] (fun x => σ x * W x i) := by
    filter_upwards [hρ,hV] with x hx hxx
    rw [hx,hxx]
  exact congrArg (fun L : X →L[ℝ] ℝ => L (axis i)) heq.fderiv_eq

/-- Integration by parts for coefficients smooth only near the compact support of the test. -/
theorem compact_scalar_local_adjoint {Ω : Set X} (hΩ : IsOpen Ω) (ρ P : X → ℝ) (V : X → X)
    (hρ : ContDiffOn ℝ ∞ ρ Ω) (hP : ContDiff ℝ ∞ P) (hV : ContDiffOn ℝ ∞ V Ω)
    (hc : HasCompactSupport P) (hsupp : tsupport P ⊆ Ω) :
    (∫ y, ρ y * fderiv ℝ P y (V y)) = -(∫ y, weightedDivergence ρ V y * P y) := by
  obtain ⟨σ,hσ,_,hσeq⟩ := exists_smooth_localization hΩ hc hsupp ρ hρ
  obtain ⟨W,hW,_,hWeq⟩ := exists_smooth_localization hΩ hc hsupp V hV
  have hleft : (fun y => σ y * fderiv ℝ P y (W y)) =
      (fun y => ρ y * fderiv ℝ P y (V y)) := by
    funext y
    by_cases hy : y ∈ tsupport P
    · rw [(hσeq y hy).eq_of_nhds, (hWeq y hy).eq_of_nhds]
    · simp [fderiv_of_notMem_tsupport (𝕜 := ℝ) hy]
  have hright : (fun y => weightedDivergence σ W y * P y) =
      (fun y => weightedDivergence ρ V y * P y) := by
    funext y
    by_cases hy : y ∈ tsupport P
    · rw [weightedDivergence_congr (hσeq y hy) (hWeq y hy)]
    · simp [image_eq_zero_of_notMem_tsupport hy]
  have hh := compact_scalar_variable_adjoint σ P W hσ hP hW hc
  rwa [hleft,hright] at hh

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

lemma tsupport_fischerPair_subset (b : ι → MvPolynomial I ℝ) (d : κ → MvPolynomial I ℝ)
    (c : X → ι → ℝ) (z : X → κ → ℝ) :
    tsupport (fun x => fischerInner (finitePolynomialField b c x) (finitePolynomialField d z x)) ⊆ tsupport c := by
  apply closure_mono
  intro x hx
  simp only [Function.mem_support] at hx ⊢
  contrapose! hx
  simp only [fischerInner_finitePolynomialField, hx, Pi.zero_apply, zero_mul, Finset.sum_const_zero]

/-- The covariant adjoint identity with the local density and vector field on the coordinate
    neighborhood. No global metric or frame extension is part of the hypotheses. -/
theorem compact_local_covariant_fischer_contraction {Ω : Set X} (hΩ : IsOpen Ω) {K : ℝ}
    {g : MetricField} (h : Elliptic Ω K g) (hK : 0 < K) (e : Frame)
    (he : ∀ i, ContDiffOn ℝ ∞ (fun x => e x i) Ω)
    (hframe : ∀ x ∈ Ω, ∀ i j, metricPair g x (e x i) (e x j) = if i = j then 1 else 0)
    (ρ : X → ℝ) (hρ : ContDiffOn ℝ ∞ ρ Ω) (V : X → X) (hV : ContDiffOn ℝ ∞ V Ω)
    (b : ι → MvPolynomial I ℝ) (d : κ → MvPolynomial I ℝ)
    (c : X → ι → ℝ) (z : X → κ → ℝ) (hc : ContDiff ℝ ∞ c) (hz : ContDiff ℝ ∞ z)
    (hcompact : HasCompactSupport c) (hsupp : tsupport c ⊆ Ω) :
    (∫ y, ρ y * (fischerInner (covariantPolynomialDerivative g e b c y (V y)) (finitePolynomialField d z y) +
      fischerInner (finitePolynomialField b c y) (covariantPolynomialDerivative g e d z y (V y)))) =
      -(∫ y, weightedDivergence ρ V y * fischerInner (finitePolynomialField b c y) (finitePolynomialField d z y)) := by
  have hh := compact_scalar_local_adjoint hΩ ρ
    (fun x => fischerInner (finitePolynomialField b c x) (finitePolynomialField d z x)) V hρ
    (contDiff_fischerPair b d c z hc hz) hV (hasCompactSupport_fischerPair b d c z hcompact)
    ((tsupport_fischerPair_subset b d c z).trans hsupp)
  simpa only [covariant_fischer_pair_derivative hΩ h hK e he hframe b d c z hc hz hsupp] using hh

/-- In particular, the integration measure and first-order direction are the actual metric
    density and a chosen orthonormal frame vector. -/
theorem compact_metric_frame_fischer_contraction {Ω : Set X} (hΩ : IsOpen Ω) {K : ℝ}
    {g : MetricField} (h : Elliptic Ω K g) (hK : 0 < K) (e : Frame)
    (he : ∀ i, ContDiffOn ℝ ∞ (fun x => e x i) Ω)
    (hframe : ∀ x ∈ Ω, ∀ i j, metricPair g x (e x i) (e x j) = if i = j then 1 else 0)
    (a : I) (b : ι → MvPolynomial I ℝ) (d : κ → MvPolynomial I ℝ)
    (c : X → ι → ℝ) (z : X → κ → ℝ) (hc : ContDiff ℝ ∞ c) (hz : ContDiff ℝ ∞ z)
    (hcompact : HasCompactSupport c) (hsupp : tsupport c ⊆ Ω) :
    (∫ y, metricDensity g y *
      (fischerInner (covariantPolynomialDerivative g e b c y (e y a)) (finitePolynomialField d z y) +
      fischerInner (finitePolynomialField b c y) (covariantPolynomialDerivative g e d z y (e y a)))) =
      -(∫ y, weightedDivergence (metricDensity g) (fun x => e x a) y *
        fischerInner (finitePolynomialField b c y) (finitePolynomialField d z y)) :=
  compact_local_covariant_fischer_contraction hΩ h hK e he hframe _ (h.contDiffOn_density hK)
    _ (he a) b d c z hc hz hcompact hsupp

end ShrinkingSpheres
