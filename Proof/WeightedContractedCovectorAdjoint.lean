import Proof.ContractedCovectorAdjoint
import Proof.CovectorCurvature

noncomputable section
open Set MeasureTheory MvPolynomial
open scoped ContDiff
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.AngularPolynomial

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

theorem compact_contracted_weighted_covector_fischer_adjoint {Ω : Set X} (hΩ : IsOpen Ω) {K : ℝ}
    {g : MetricField} (h : Elliptic Ω K g) (hK : 0 < K) (e : Frame)
    (he : ∀ i, ContDiffOn ℝ ∞ (fun x => e x i) Ω)
    (hframe : ∀ x ∈ Ω, ∀ i j, metricPair g x (e x i) (e x j) = if i = j then 1 else 0)
    (b : ι → MvPolynomial I ℝ) (d : κ → I → MvPolynomial I ℝ)
    (c : X → ι → ℝ) (z : X → κ → ℝ) (f : X → ℝ) (k s : ℝ)
    (hc : ContDiff ℝ ∞ c) (hz : ContDiff ℝ ∞ z) (hf : ContDiffOn ℝ ∞ f Ω)
    (hcompact : HasCompactSupport c) (hsupp : tsupport c ⊆ Ω) :
    (∫ x, metricDensity g x * (∑ i, fischerInner (weightedPolynomialDerivative g e b c f k s x (e x i))
      (finitePolynomialField (fun a => d a i) z x))) =
      (∫ x, metricDensity g x * (∑ i, fischerInner (finitePolynomialField b c x)
        (weightedCovectorPolynomialDerivative g e d z f k (-s) x (e x i) i))) := by
  let ρ := metricDensity g
  have hρ := h.contDiffOn_density hK
  let A := fun x => ρ x * ∑ i, fischerInner (covariantPolynomialDerivative g e b c x (e x i))
    (finitePolynomialField (fun a => d a i) z x)
  let B := fun x => ρ x * ∑ i, fischerInner (finitePolynomialField b c x)
    (covectorPolynomialDerivative g e d z x (e x i) i)
  let W := fun x => ρ x * ∑ i, (k*fderiv ℝ f x (e x i)) *
    fischerInner (finitePolynomialField b c x) (finitePolynomialField (fun a => d a i) z x)
  have hA : Integrable A := by
    simp only [A, Finset.mul_sum]
    exact integrable_finsetSum _ (fun i _ => integrable_covariant_fischer_left hΩ h hK e he _ (he i)
      ρ hρ b _ c z hc.contDiffOn hz.contDiffOn hcompact hsupp)
  have hB : Integrable B := by
    apply integrable_local_supported hΩ c hcompact hsupp B
      (hρ.mul (ContDiffOn.sum (fun i _ => contDiffOn_covector_fischer_right hΩ h hK e he _ (he i)
        b d c z hc.contDiffOn hz.contDiffOn i)))
    intro x hx
    simp [B, finitePolynomialField_zero_outside b c hx, fischerInner_zero_left]
  have hW : Integrable W := by
    simp only [W, Finset.mul_sum]
    apply integrable_finsetSum
    intro i _
    have hw : ContDiffOn ℝ ∞ (fun x => k*fderiv ℝ f x (e x i)) Ω :=
      contDiffOn_const.mul ((hf.fderiv_of_isOpen hΩ (by simp)).clm_apply (he i))
    have hh := integrable_weighted_fischerPair_local hΩ (fun x => ρ x * (k*fderiv ℝ f x (e x i)))
      (hρ.mul hw) b (fun a => d a i) c z hc.contDiffOn hz.contDiffOn hcompact hsupp
    simpa only [mul_assoc] using hh
  have hab : (∫ x, A x) = -(∫ x, B x) :=
    compact_contracted_covector_fischer_adjoint hΩ h hK e he hframe b d c z hc hz hcompact hsupp
  have hl : (fun x => ρ x * ∑ i, fischerInner (weightedPolynomialDerivative g e b c f k s x (e x i))
      (finitePolynomialField (fun a => d a i) z x)) = fun x => s*A x + W x := by
    funext x
    simp only [weightedPolynomialDerivative, fischerInner_add_left, fischerInner_C_mul_left, A, W, Fin.sum_univ_three]
    ring
  have hr : (fun x => ρ x * ∑ i, fischerInner (finitePolynomialField b c x)
      (weightedCovectorPolynomialDerivative g e d z f k (-s) x (e x i) i)) = fun x => (-s)*B x + W x := by
    funext x
    simp only [weightedCovectorPolynomialDerivative, fischerInner_add_right, fischerInner_C_mul_right, B, W, Fin.sum_univ_three]
    ring
  change (∫ x, ρ x * _) = ∫ x, ρ x * _
  rw [hl, hr, integral_add (hA.const_mul s) hW, integral_add (hB.const_mul (-s)) hW,
    integral_const_mul, integral_const_mul, hab]
  ring

end ShrinkingSpheres
