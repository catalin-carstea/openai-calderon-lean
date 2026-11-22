module

public import Proof.CalderonN.ContractedCovectorAdjoint
public import Proof.CalderonN.CovectorCurvature
import Mathlib.Tactic

@[expose] public section

/- Port of TensorFischer.lean from the checked Proposition 5.3 release f308cb9d. -/
noncomputable section
open Set Filter MeasureTheory MvPolynomial
open scoped ContDiff Topology
namespace CalderonN
variable {n : ℕ}
variable [NeZero n]

open Set MeasureTheory MvPolynomial

open OAI.AnisotropicCalderon.AngularPolynomial

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

def tensorPolynomialDerivative (g : (MetricField n)) (e : (Frame n))
    (b : ι → (I n) → (I n) → MvPolynomial (I n) ℝ) (c : (X n) → ι → ℝ) (y a : (X n)) (i j : (I n)) : MvPolynomial (I n) ℝ :=
  covectorPolynomialDerivative g e (fun t h => b t i h) c y a j -
    ∑ h, C (frameConnectionCoefficient g e y a i h) * finitePolynomialField (fun t => b t h j) c y

lemma contDiffOn_tensor_fischer_right {Ω : Set (X n)} (hΩ : IsOpen Ω) {K : ℝ}
    {g : (MetricField n)} (h : Elliptic Ω K g) (hK : 0 < K) (e : (Frame n))
    (he : ∀ i, ContDiffOn ℝ ∞ (fun x => e x i) Ω) (V : (X n) → (X n)) (hV : ContDiffOn ℝ ∞ V Ω)
    (b : ι → MvPolynomial (I n) ℝ) (d : κ → (I n) → (I n) → MvPolynomial (I n) ℝ)
    (c : (X n) → ι → ℝ) (z : (X n) → κ → ℝ) (hc : ContDiffOn ℝ ∞ c Ω) (hz : ContDiffOn ℝ ∞ z Ω) (i j : (I n)) :
    ContDiffOn ℝ ∞ (fun x => fischerInner (finitePolynomialField b c x)
      (tensorPolynomialDerivative g e d z x (V x) i j)) Ω := by
  simp only [tensorPolynomialDerivative, fischerInner_sub_right, fischerInner_sum_right, fischerInner_C_mul_right]
  exact (contDiffOn_covector_fischer_right hΩ h hK e he V hV b (fun t a => d t i a) c z hc hz j).sub
    (ContDiffOn.sum (fun a _ => (h.contDiffOn_frameConnection hΩ hK e he V hV i a).mul
      (contDiffOn_fischerPair b (fun t => d t a j) c z hc hz)))

theorem compact_covector_fischer_adjoint {Ω : Set (X n)} (hΩ : IsOpen Ω) {K : ℝ}
    {g : (MetricField n)} (h : Elliptic Ω K g) (hK : 0 < K) (e : (Frame n))
    (he : ∀ i, ContDiffOn ℝ ∞ (fun x => e x i) Ω)
    (hframe : ∀ x ∈ Ω, ∀ i j, metricPair g x (e x i) (e x j) = if i = j then 1 else 0)
    (ρ : (X n) → ℝ) (hρ : ContDiffOn ℝ ∞ ρ Ω) (V : (X n) → (X n)) (hV : ContDiffOn ℝ ∞ V Ω)
    (b : ι → (I n) → MvPolynomial (I n) ℝ) (d : κ → (I n) → MvPolynomial (I n) ℝ)
    (c : (X n) → ι → ℝ) (z : (X n) → κ → ℝ) (hc : ContDiff ℝ ∞ c) (hz : ContDiff ℝ ∞ z)
    (hcompact : HasCompactSupport c) (hsupp : tsupport c ⊆ Ω) :
    (∫ x, ρ x * ∑ j, fischerInner (covectorPolynomialDerivative g e b c x (V x) j)
      (finitePolynomialField (fun t => d t j) z x)) =
      -(∫ x, ρ x * ∑ j, fischerInner (finitePolynomialField (fun t => b t j) c x)
        (covectorPolynomialDerivative g e d z x (V x) j)) -
      (∫ x, weightedDivergence ρ V x * finiteCovectorFischerPair b d c z x) := by
  have hA : Integrable (fun x => ρ x * ∑ j, fischerInner (covectorPolynomialDerivative g e b c x (V x) j)
      (finitePolynomialField (fun t => d t j) z x)) := by
    apply integrable_local_supported hΩ c hcompact hsupp _
      (hρ.mul (ContDiffOn.sum (fun j _ => contDiffOn_covector_fischer_left hΩ h hK e he V hV b _ c z hc.contDiffOn hz.contDiffOn j)))
    intro x hx
    simp [covectorPolynomialDerivative_zero_outside g e b c hx, fischerInner_zero_left]
  have hB : Integrable (fun x => ρ x * ∑ j, fischerInner (finitePolynomialField (fun t => b t j) c x)
      (covectorPolynomialDerivative g e d z x (V x) j)) := by
    apply integrable_local_supported hΩ c hcompact hsupp _
      (hρ.mul (ContDiffOn.sum (fun j _ => contDiffOn_covector_fischer_right hΩ h hK e he V hV _ d c z hc.contDiffOn hz.contDiffOn j)))
    intro x hx
    simp [finitePolynomialField_zero_outside _ c hx, fischerInner_zero_left]
  have hh := compact_local_covector_fischer_contraction hΩ h hK e he hframe ρ hρ V hV b d c z hc hz hcompact hsupp
  have hfun : (fun x => ρ x * ∑ j, (fischerInner (covectorPolynomialDerivative g e b c x (V x) j)
      (finitePolynomialField (fun t => d t j) z x) +
      fischerInner (finitePolynomialField (fun t => b t j) c x) (covectorPolynomialDerivative g e d z x (V x) j))) =
      fun x => (ρ x * ∑ j, fischerInner (covectorPolynomialDerivative g e b c x (V x) j)
        (finitePolynomialField (fun t => d t j) z x)) +
        (ρ x * ∑ j, fischerInner (finitePolynomialField (fun t => b t j) c x) (covectorPolynomialDerivative g e d z x (V x) j)) := by
    funext x
    rw [Finset.sum_add_distrib, mul_add]
  rw [hfun, integral_add hA hB] at hh
  linarith

lemma tensor_contraction_eq_row_divergence {Ω : Set (X n)} (hΩ : IsOpen Ω) {K : ℝ}
    {g : (MetricField n)} (h : Elliptic Ω K g) (hK : 0 < K) (e : (Frame n))
    (he : ∀ i, ContDiffOn ℝ ∞ (fun x => e x i) Ω)
    (hframe : ∀ x ∈ Ω, ∀ i j, metricPair g x (e x i) (e x j) = if i = j then 1 else 0)
    (b : ι → (I n) → MvPolynomial (I n) ℝ) (d : κ → (I n) → (I n) → MvPolynomial (I n) ℝ)
    (c : (X n) → ι → ℝ) (z : (X n) → κ → ℝ) {y : (X n)} (hy : y ∈ Ω) :
    metricDensity g y * (∑ i, ∑ j, fischerInner (finitePolynomialField (fun t => b t j) c y)
      (tensorPolynomialDerivative g e d z y (e y i) i j)) =
      (∑ i, metricDensity g y * ∑ j, fischerInner (finitePolynomialField (fun t => b t j) c y)
        (covectorPolynomialDerivative g e (fun t a => d t i a) z y (e y i) j)) +
      (∑ i, weightedDivergence (metricDensity g) (fun x => e x i) y *
        finiteCovectorFischerPair b (fun t a => d t i a) c z y) := by
  let w := fun v i a => frameConnectionCoefficient g e y (e y v) i a
  let P := fun i j => fischerInner (finitePolynomialField (fun t => b t j) c y)
    (finitePolynomialField (fun t => d t i j) z y)
  have hh := frame_connection_trace_cancellation w
    (fun v a t => frameConnection_skew hΩ h hK e he hframe hy (e y v) a t)
    (fun i => ∑ j, P i j)
  have hC : (∑ i, ∑ j, ∑ a, w i i a * P a j) =
      ∑ i, ∑ a, w i i a * ∑ j, P a j := by
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_comm (s := Finset.univ) (t := Finset.univ)
      (f := fun j a => w i i a * P a j)]
    exact Finset.sum_congr rfl fun a _ => (Finset.mul_sum Finset.univ (fun j => P a j) (w i i a)).symm
  rw [Finset.mul_sum]
  simp only [tensorPolynomialDerivative, fischerInner_sub_right, fischerInner_sum_right,
    fischerInner_C_mul_right, Finset.sum_sub_distrib, ← Finset.mul_sum, finiteCovectorFischerPair,
    weightedDivergence_frame hΩ h hK e he hy (hframe y hy)]
  have hρ : (∑ i, (metricDensity g y * ∑ a, w a i a) * ∑ j, P i j) =
      metricDensity g y * ∑ i, (∑ a, w a i a) * ∑ j, P i j := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun i _ => mul_assoc _ _ _)
  rw [mul_sub]
  change _ - metricDensity g y * (∑ i, ∑ j, ∑ a, w i i a * P a j) =
    _ + (∑ i, (metricDensity g y * ∑ a, w a i a) * ∑ j, P i j)
  rw [hC, hρ, hh]
  ring


theorem compact_contracted_tensor_fischer_adjoint {Ω : Set (X n)} (hΩ : IsOpen Ω) {K : ℝ}
    {g : (MetricField n)} (h : Elliptic Ω K g) (hK : 0 < K) (e : (Frame n))
    (he : ∀ i, ContDiffOn ℝ ∞ (fun x => e x i) Ω)
    (hframe : ∀ x ∈ Ω, ∀ i j, metricPair g x (e x i) (e x j) = if i = j then 1 else 0)
    (b : ι → (I n) → MvPolynomial (I n) ℝ) (d : κ → (I n) → (I n) → MvPolynomial (I n) ℝ)
    (c : (X n) → ι → ℝ) (z : (X n) → κ → ℝ) (hc : ContDiff ℝ ∞ c) (hz : ContDiff ℝ ∞ z)
    (hcompact : HasCompactSupport c) (hsupp : tsupport c ⊆ Ω) :
    (∫ x, metricDensity g x * (∑ i, ∑ j, fischerInner (covectorPolynomialDerivative g e b c x (e x i) j)
      (finitePolynomialField (fun t => d t i j) z x))) =
      -(∫ x, metricDensity g x * (∑ i, ∑ j, fischerInner (finitePolynomialField (fun t => b t j) c x)
        (tensorPolynomialDerivative g e d z x (e x i) i j))) := by
  let ρ := metricDensity g
  have hρ := h.contDiffOn_density hK
  let A := fun i x => ρ x * ∑ j, fischerInner (covectorPolynomialDerivative g e b c x (e x i) j)
    (finitePolynomialField (fun t => d t i j) z x)
  let B := fun i x => ρ x * ∑ j, fischerInner (finitePolynomialField (fun t => b t j) c x)
    (covectorPolynomialDerivative g e (fun t a => d t i a) z x (e x i) j)
  let D := fun i x => weightedDivergence ρ (fun y => e y i) x * finiteCovectorFischerPair b (fun t a => d t i a) c z x
  have hA (i : (I n)) : Integrable (A i) := by
    apply integrable_local_supported hΩ c hcompact hsupp (A i)
      (hρ.mul (ContDiffOn.sum (fun j _ => contDiffOn_covector_fischer_left hΩ h hK e he _ (he i) b _ c z hc.contDiffOn hz.contDiffOn j)))
    intro x hx
    simp [A, covectorPolynomialDerivative_zero_outside g e b c hx, fischerInner_zero_left]
  have hB (i : (I n)) : Integrable (B i) := by
    apply integrable_local_supported hΩ c hcompact hsupp (B i)
      (hρ.mul (ContDiffOn.sum (fun j _ => contDiffOn_covector_fischer_right hΩ h hK e he _ (he i) _ _ c z hc.contDiffOn hz.contDiffOn j)))
    intro x hx
    simp [B, finitePolynomialField_zero_outside _ c hx, fischerInner_zero_left]
  have hD (i : (I n)) : Integrable (D i) := by
    apply integrable_local_supported hΩ c hcompact hsupp (D i)
      ((contDiffOn_weightedDivergence hΩ ρ _ hρ (he i)).mul (ContDiffOn.sum (fun j _ =>
        contDiffOn_fischerPair (fun t => b t j) (fun t => d t i j) c z hc.contDiffOn hz.contDiffOn)))
    intro x hx
    simp [D, finiteCovectorFischerPair, finitePolynomialField_zero_outside _ c hx, fischerInner_zero_left]
  have hi (i : (I n)) : (∫ x, A i x) = -(∫ x, B i x) - ∫ x, D i x :=
    compact_covector_fischer_adjoint hΩ h hK e he hframe ρ hρ _ (he i) b _ c z hc hz hcompact hsupp
  have hs : (∫ x, ∑ i : (I n), A i x) = -(∫ x, ∑ i : (I n), B i x) - ∫ x, ∑ i : (I n), D i x := by
    rw [integral_finsetSum _ (fun i _ => hA i), integral_finsetSum _ (fun i _ => hB i),
      integral_finsetSum _ (fun i _ => hD i), ← Finset.sum_neg_distrib, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl (fun i _ => hi i)
  have hBsum := integrable_finsetSum Finset.univ (fun i _ => hB i)
  have hDsum := integrable_finsetSum Finset.univ (fun i _ => hD i)
  have hright : (fun x => ρ x * ∑ i, ∑ j, fischerInner (finitePolynomialField (fun t => b t j) c x)
      (tensorPolynomialDerivative g e d z x (e x i) i j)) = fun x => (∑ i : (I n), B i x) + ∑ i : (I n), D i x := by
    funext x
    by_cases hx : x ∈ Ω
    · exact tensor_contraction_eq_row_divergence hΩ h hK e he hframe b d c z hx
    · have hout : x ∉ tsupport c := fun ht => hx (hsupp ht)
      simp [B, D, finiteCovectorFischerPair, finitePolynomialField_zero_outside _ c hout, fischerInner_zero_left]
  have hleft : (fun x => ρ x * ∑ i, ∑ j, fischerInner (covectorPolynomialDerivative g e b c x (e x i) j)
      (finitePolynomialField (fun t => d t i j) z x)) = fun x => ∑ i : (I n), A i x := by
    funext x
    simp only [A, Finset.mul_sum]
  change (∫ x, ρ x * _) = -(∫ x, ρ x * _)
  rw [hleft, hright, integral_add hBsum hDsum]
  linarith

end CalderonN
