module

public import Proof.CalderonN.PolynomialDerivativeFields
public import Proof.CalderonN.DensityDivergence
import Mathlib.Tactic

@[expose] public section

/- Port of FischerAdjoint.lean from the checked Proposition 5.3 release f308cb9d. -/
noncomputable section
open Set Filter MeasureTheory MvPolynomial
open scoped ContDiff Topology
namespace CalderonN
variable {n : ℕ} [NeZero n]

open OAI.AnisotropicCalderon.AngularPolynomial

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

lemma contDiffOn_fischerPair {Ω : Set (X n)} (b : ι → MvPolynomial (I n) ℝ) (d : κ → MvPolynomial (I n) ℝ)
    (c : (X n) → ι → ℝ) (z : (X n) → κ → ℝ) (hc : ContDiffOn ℝ ∞ c Ω) (hz : ContDiffOn ℝ ∞ z Ω) :
    ContDiffOn ℝ ∞ (fun x => fischerInner (finitePolynomialField b c x) (finitePolynomialField d z x)) Ω := by
  have hfun : (fun x => fischerInner (finitePolynomialField b c x) (finitePolynomialField d z x)) =
      (fun x => polynomialFamilyFischerBilinear b d (c x) (z x)) := by
    funext x
    rw [fischerInner_finitePolynomialField, polynomialFamilyFischerBilinear_apply]
  rw [hfun]
  exact ((polynomialFamilyFischerBilinear b d).contDiff.comp_contDiffOn hc).clm_apply hz

lemma integrable_weighted_fischerPair_local {Ω : Set (X n)} (hΩ : IsOpen Ω)
    (ρ : (X n) → ℝ) (hρ : ContDiffOn ℝ ∞ ρ Ω)
    (b : ι → MvPolynomial (I n) ℝ) (d : κ → MvPolynomial (I n) ℝ)
    (c : (X n) → ι → ℝ) (z : (X n) → κ → ℝ) (hc : ContDiffOn ℝ ∞ c Ω) (hz : ContDiffOn ℝ ∞ z Ω)
    (hcompact : HasCompactSupport c) (hsupp : tsupport c ⊆ Ω) :
    Integrable (fun x => ρ x * fischerInner (finitePolynomialField b c x) (finitePolynomialField d z x)) := by
  have hs : tsupport (fun x => ρ x * fischerInner (finitePolynomialField b c x) (finitePolynomialField d z x)) ⊆
      tsupport c := by
    apply closure_minimal _ (isClosed_tsupport c)
    intro x hx
    by_contra hout
    have hc0 := image_eq_zero_of_notMem_tsupport hout
    apply hx
    simp [finitePolynomialField, hc0, fischerInner_zero_left]
  have hreg := contDiff_of_tsupport_subset hΩ _
    (hρ.mul (contDiffOn_fischerPair b d c z hc hz)) (hs.trans hsupp)
  exact hreg.continuous.integrable_of_hasCompactSupport
    (hcompact.of_isClosed_subset (isClosed_tsupport _) hs)

lemma contDiffOn_weightedDivergence {Ω : Set (X n)} (hΩ : IsOpen Ω) (ρ : (X n) → ℝ) (V : (X n) → (X n))
    (hρ : ContDiffOn ℝ ∞ ρ Ω) (hV : ContDiffOn ℝ ∞ V Ω) :
    ContDiffOn ℝ ∞ (weightedDivergence ρ V) Ω :=
  ContDiffOn.sum (fun i _ =>
    (((hρ.mul (contDiffOn_vector_component V hV i)).fderiv_of_isOpen hΩ (by simp)).clm_apply contDiffOn_const))

/-- The formal adjoint of covariant differentiation includes the divergence of its actual
    spatial direction. Every coefficient hypothesis is local to the coordinate neighborhood. -/
theorem compact_covariant_fischer_adjoint {Ω : Set (X n)} (hΩ : IsOpen Ω) {K : ℝ}
    {g : (MetricField n)} (h : Elliptic Ω K g) (hK : 0 < K) (e : (Frame n))
    (he : ∀ i, ContDiffOn ℝ ∞ (fun x => e x i) Ω)
    (hframe : ∀ x ∈ Ω, ∀ i j, metricPair g x (e x i) (e x j) = if i = j then 1 else 0)
    (ρ : (X n) → ℝ) (hρ : ContDiffOn ℝ ∞ ρ Ω) (V : (X n) → (X n)) (hV : ContDiffOn ℝ ∞ V Ω)
    (b : ι → MvPolynomial (I n) ℝ) (d : κ → MvPolynomial (I n) ℝ)
    (c : (X n) → ι → ℝ) (z : (X n) → κ → ℝ) (hc : ContDiff ℝ ∞ c) (hz : ContDiff ℝ ∞ z)
    (hcompact : HasCompactSupport c) (hsupp : tsupport c ⊆ Ω) :
    (∫ x, ρ x * fischerInner (covariantPolynomialDerivative g e b c x (V x)) (finitePolynomialField d z x)) =
      -(∫ x, ρ x * fischerInner (finitePolynomialField b c x) (covariantPolynomialDerivative g e d z x (V x)) +
        weightedDivergence ρ V x * fischerInner (finitePolynomialField b c x) (finitePolynomialField d z x)) := by
  obtain ⟨hDc,hDcompact,hDsupp⟩ := derivativeCoefficientFamily_smooth_compact hΩ h hK e he c V hc hV hcompact hsupp
  have hleft := integrable_weighted_fischerPair_local hΩ ρ hρ (derivativePolynomialFamily b) d
    (derivativeCoefficientFamily g e c V) z hDc.contDiffOn hz.contDiffOn hDcompact (hDsupp.trans hsupp)
  have hright := integrable_weighted_fischerPair_local hΩ ρ hρ b (derivativePolynomialFamily d)
    c (derivativeCoefficientFamily g e z V) hc.contDiffOn
    (derivativeCoefficientFamily_smoothOn hΩ h hK e he z V hz.contDiffOn hV) hcompact hsupp
  simp only [← covariantPolynomialDerivative_eq_augmented] at hleft hright
  have hdiv := integrable_weighted_fischerPair_local hΩ _
    (contDiffOn_weightedDivergence hΩ ρ V hρ hV) b d c z hc.contDiffOn hz.contDiffOn hcompact hsupp
  have hh := compact_local_covariant_fischer_contraction hΩ h hK e he hframe ρ hρ V hV b d c z hc hz hcompact hsupp
  simp_rw [mul_add] at hh
  rw [integral_add hleft hright] at hh
  rw [integral_add hright hdiv]
  linarith

end CalderonN
