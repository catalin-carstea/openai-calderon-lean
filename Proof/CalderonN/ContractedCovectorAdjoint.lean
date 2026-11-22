module

public import Proof.CalderonN.LocalFischerRegularity
import Mathlib.Tactic

@[expose] public section

/- Port of ContractedCovectorAdjoint.lean from the checked Proposition 5.3 release f308cb9d. -/
noncomputable section
open Set Filter MeasureTheory MvPolynomial
open scoped ContDiff Topology
namespace CalderonN
variable {n : ℕ}

variable [NeZero n]
open Set MeasureTheory MvPolynomial

open OAI.AnisotropicCalderon.AngularPolynomial

lemma frame_connection_trace_cancellation (w : (I n) → (I n) → (I n) → ℝ)
    (hw : ∀ v i j, w v i j = -w v j i) (P : (I n) → ℝ) :
    (∑ i, (∑ a, w a i a) * P i) = -(∑ i, ∑ a, w i i a * P a) := by
  simp only [Finset.sum_mul]
  rw [Finset.sum_comm]
  simp only [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro a _
  rw [hw i a i, neg_mul]

lemma weightedDivergence_frame {Ω : Set (X n)} (hΩ : IsOpen Ω) {K : ℝ} {g : (MetricField n)}
    (h : Elliptic Ω K g) (hK : 0 < K) (e : (Frame n))
    (he : ∀ i, ContDiffOn ℝ ∞ (fun x => e x i) Ω) {y : (X n)} (hy : y ∈ Ω)
    (hframe : ∀ i j, metricPair g y (e y i) (e y j) = if i = j then 1 else 0) (i : (I n)) :
    weightedDivergence (metricDensity g) (fun x => e x i) y =
      metricDensity g y * ∑ a, frameConnectionCoefficient g e y (e y a) i a := by
  rw [weightedDivergence_metric_frame hΩ h hK e hy hframe _
    (((he i).contDiffAt (hΩ.mem_nhds hy)).differentiableAt (by simp))]
  rfl

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

lemma covector_contraction_eq_scalar_divergence {Ω : Set (X n)} (hΩ : IsOpen Ω) {K : ℝ}
    {g : (MetricField n)} (h : Elliptic Ω K g) (hK : 0 < K) (e : (Frame n))
    (he : ∀ i, ContDiffOn ℝ ∞ (fun x => e x i) Ω)
    (hframe : ∀ x ∈ Ω, ∀ i j, metricPair g x (e x i) (e x j) = if i = j then 1 else 0)
    (b : ι → MvPolynomial (I n) ℝ) (d : κ → (I n) → MvPolynomial (I n) ℝ)
    (c : (X n) → ι → ℝ) (z : (X n) → κ → ℝ) {y : (X n)} (hy : y ∈ Ω) :
    metricDensity g y * (∑ i, fischerInner (finitePolynomialField b c y)
      (covectorPolynomialDerivative g e d z y (e y i) i)) =
      (∑ i, metricDensity g y * fischerInner (finitePolynomialField b c y)
        (covariantPolynomialDerivative g e (fun a => d a i) z y (e y i))) +
      (∑ i, weightedDivergence (metricDensity g) (fun x => e x i) y *
        fischerInner (finitePolynomialField b c y) (finitePolynomialField (fun a => d a i) z y)) := by
  have hh := frame_connection_trace_cancellation
    (fun v i j => frameConnectionCoefficient g e y (e y v) i j)
    (fun v i j => frameConnection_skew hΩ h hK e he hframe hy (e y v) i j)
    (fun i => fischerInner (finitePolynomialField b c y) (finitePolynomialField (fun a => d a i) z y))
  rw [Finset.mul_sum]
  simp only [covectorPolynomialDerivative, fischerInner_sub_right, fischerInner_sum_right,
    fischerInner_C_mul_right, mul_sub, Finset.sum_sub_distrib, ← Finset.mul_sum,
    weightedDivergence_frame hΩ h hK e he hy (hframe y hy)]
  simp only [mul_assoc]
  rw [← Finset.mul_sum, hh]
  ring


/-- Full contraction removes the frame divergence term through the lower covector index. -/
theorem compact_contracted_covector_fischer_adjoint {Ω : Set (X n)} (hΩ : IsOpen Ω) {K : ℝ}
    {g : (MetricField n)} (h : Elliptic Ω K g) (hK : 0 < K) (e : (Frame n))
    (he : ∀ i, ContDiffOn ℝ ∞ (fun x => e x i) Ω)
    (hframe : ∀ x ∈ Ω, ∀ i j, metricPair g x (e x i) (e x j) = if i = j then 1 else 0)
    (b : ι → MvPolynomial (I n) ℝ) (d : κ → (I n) → MvPolynomial (I n) ℝ)
    (c : (X n) → ι → ℝ) (z : (X n) → κ → ℝ) (hc : ContDiff ℝ ∞ c) (hz : ContDiff ℝ ∞ z)
    (hcompact : HasCompactSupport c) (hsupp : tsupport c ⊆ Ω) :
    (∫ x, metricDensity g x * (∑ i, fischerInner (covariantPolynomialDerivative g e b c x (e x i))
      (finitePolynomialField (fun a => d a i) z x))) =
      -(∫ x, metricDensity g x * (∑ i, fischerInner (finitePolynomialField b c x)
        (covectorPolynomialDerivative g e d z x (e x i) i))) := by
  let ρ := metricDensity g
  have hρ := h.contDiffOn_density hK
  let A := fun i x => ρ x * fischerInner (covariantPolynomialDerivative g e b c x (e x i))
    (finitePolynomialField (fun a => d a i) z x)
  let B := fun i x => ρ x * fischerInner (finitePolynomialField b c x)
    (covariantPolynomialDerivative g e (fun a => d a i) z x (e x i))
  let D := fun i x => weightedDivergence ρ (fun y => e y i) x *
    fischerInner (finitePolynomialField b c x) (finitePolynomialField (fun a => d a i) z x)
  have hA (i : (I n)) : Integrable (A i) := integrable_covariant_fischer_left hΩ h hK e he _ (he i)
    ρ hρ b _ c z hc.contDiffOn hz.contDiffOn hcompact hsupp
  have hB (i : (I n)) : Integrable (B i) := integrable_covariant_fischer_right hΩ h hK e he _ (he i)
    ρ hρ b _ c z hc.contDiffOn hz.contDiffOn hcompact hsupp
  have hD (i : (I n)) : Integrable (D i) := integrable_weighted_fischerPair_local hΩ _
    (contDiffOn_weightedDivergence hΩ ρ _ hρ (he i)) b _ c z hc.contDiffOn hz.contDiffOn hcompact hsupp
  have hi (i : (I n)) : (∫ x, A i x) = -(∫ x, B i x) - (∫ x, D i x) := by
    have hh := compact_covariant_fischer_adjoint hΩ h hK e he hframe ρ hρ _ (he i)
      b (fun a => d a i) c z hc hz hcompact hsupp
    change (∫ x, A i x) = -(∫ x, B i x + D i x) at hh
    rw [integral_add (hB i) (hD i)] at hh
    linarith
  have hs : (∫ x, ∑ i : (I n), A i x) = -(∫ x, ∑ i : (I n), B i x) - (∫ x, ∑ i : (I n), D i x) := by
    rw [integral_finsetSum _ (fun i _ => hA i), integral_finsetSum _ (fun i _ => hB i),
      integral_finsetSum _ (fun i _ => hD i), ← Finset.sum_neg_distrib, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl (fun i _ => hi i)
  have hBsum := integrable_finsetSum Finset.univ (fun i _ => hB i)
  have hDsum := integrable_finsetSum Finset.univ (fun i _ => hD i)
  have hright : (fun x => ρ x * ∑ i, fischerInner (finitePolynomialField b c x)
      (covectorPolynomialDerivative g e d z x (e x i) i)) =
      fun x => (∑ i : (I n), B i x) + ∑ i : (I n), D i x := by
    funext x
    by_cases hx : x ∈ Ω
    · exact covector_contraction_eq_scalar_divergence hΩ h hK e he hframe b d c z hx
    · have hout : x ∉ tsupport c := fun ht => hx (hsupp ht)
      simp [B, D, finitePolynomialField_zero_outside b c hout, fischerInner_zero_left]
  have hleft : (fun x => ρ x * ∑ i, fischerInner (covariantPolynomialDerivative g e b c x (e x i))
      (finitePolynomialField (fun a => d a i) z x)) = fun x => ∑ i : (I n), A i x := by
    funext x
    simp only [A, Finset.mul_sum]
  change (∫ x, ρ x * _) = -(∫ x, ρ x * _)
  rw [hleft, hright, integral_add hBsum hDsum]
  linarith

end CalderonN
