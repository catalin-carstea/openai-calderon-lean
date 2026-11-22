module

public import Proof.CalderonN.TensorFischer
import Mathlib.Tactic

@[expose] public section

/- Port of WeightedTensorFischer.lean from the checked Proposition 5.3 release f308cb9d. -/
noncomputable section
open Set Filter MeasureTheory MvPolynomial
open scoped ContDiff Topology
namespace CalderonN
variable {n : ℕ}
variable [NeZero n]

open Set MeasureTheory MvPolynomial

open OAI.AnisotropicCalderon.AngularPolynomial

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

def weightedTensorPolynomialDerivative (g : (MetricField n)) (e : (Frame n))
    (b : ι → (I n) → (I n) → MvPolynomial (I n) ℝ) (c : (X n) → ι → ℝ) (f : (X n) → ℝ)
    (k s : ℝ) (y a : (X n)) (i j : (I n)) : MvPolynomial (I n) ℝ :=
  C s * tensorPolynomialDerivative g e b c y a i j +
    C (k*fderiv ℝ f y a) * finitePolynomialField (fun t => b t i j) c y

lemma contDiffOn_weightedTensor_fischer_right {Ω : Set (X n)} (hΩ : IsOpen Ω) {K : ℝ}
    {g : (MetricField n)} (h : Elliptic Ω K g) (hK : 0 < K) (e : (Frame n))
    (he : ∀ i, ContDiffOn ℝ ∞ (fun x => e x i) Ω) (V : (X n) → (X n)) (hV : ContDiffOn ℝ ∞ V Ω)
    (b : ι → MvPolynomial (I n) ℝ) (d : κ → (I n) → (I n) → MvPolynomial (I n) ℝ)
    (c : (X n) → ι → ℝ) (z : (X n) → κ → ℝ) (f : (X n) → ℝ) (k s : ℝ)
    (hc : ContDiffOn ℝ ∞ c Ω) (hz : ContDiffOn ℝ ∞ z Ω) (hf : ContDiffOn ℝ ∞ f Ω) (i j : (I n)) :
    ContDiffOn ℝ ∞ (fun x => fischerInner (finitePolynomialField b c x)
      (weightedTensorPolynomialDerivative g e d z f k s x (V x) i j)) Ω := by
  simp only [weightedTensorPolynomialDerivative, fischerInner_add_right, fischerInner_C_mul_right]
  exact (contDiffOn_const.mul (contDiffOn_tensor_fischer_right hΩ h hK e he V hV b d c z hc hz i j)).add
    ((contDiffOn_const.mul ((hf.fderiv_of_isOpen hΩ (by simp)).clm_apply hV)).mul
      (contDiffOn_fischerPair b (fun a => d a i j) c z hc hz))

theorem compact_contracted_weighted_tensor_fischer_adjoint {Ω : Set (X n)} (hΩ : IsOpen Ω) {K : ℝ}
    {g : (MetricField n)} (h : Elliptic Ω K g) (hK : 0 < K) (e : (Frame n))
    (he : ∀ i, ContDiffOn ℝ ∞ (fun x => e x i) Ω)
    (hframe : ∀ x ∈ Ω, ∀ i j, metricPair g x (e x i) (e x j) = if i = j then 1 else 0)
    (b : ι → (I n) → MvPolynomial (I n) ℝ) (d : κ → (I n) → (I n) → MvPolynomial (I n) ℝ)
    (c : (X n) → ι → ℝ) (z : (X n) → κ → ℝ) (f : (X n) → ℝ) (k s : ℝ)
    (hc : ContDiff ℝ ∞ c) (hz : ContDiff ℝ ∞ z) (hf : ContDiffOn ℝ ∞ f Ω)
    (hcompact : HasCompactSupport c) (hsupp : tsupport c ⊆ Ω) :
    (∫ x, metricDensity g x * (∑ i, ∑ j, fischerInner
      (weightedCovectorPolynomialDerivative g e b c f k s x (e x i) j)
      (finitePolynomialField (fun t => d t i j) z x))) =
      (∫ x, metricDensity g x * (∑ i, ∑ j, fischerInner
        (finitePolynomialField (fun t => b t j) c x)
        (weightedTensorPolynomialDerivative g e d z f k (-s) x (e x i) i j))) := by
  let ρ := metricDensity g
  have hρ := h.contDiffOn_density hK
  let A := fun x => ρ x * ∑ i, ∑ j, fischerInner (covectorPolynomialDerivative g e b c x (e x i) j)
    (finitePolynomialField (fun t => d t i j) z x)
  let B := fun x => ρ x * ∑ i, ∑ j, fischerInner (finitePolynomialField (fun t => b t j) c x)
    (tensorPolynomialDerivative g e d z x (e x i) i j)
  let W := fun x => ρ x * ∑ i, ∑ j, (k*fderiv ℝ f x (e x i)) *
    fischerInner (finitePolynomialField (fun t => b t j) c x) (finitePolynomialField (fun t => d t i j) z x)
  have hA : Integrable A := by
    apply integrable_local_supported hΩ c hcompact hsupp A
      (hρ.mul (ContDiffOn.sum (fun i _ => ContDiffOn.sum (fun j _ =>
        contDiffOn_covector_fischer_left hΩ h hK e he _ (he i) b _ c z hc.contDiffOn hz.contDiffOn j))))
    intro x hx
    simp [A, covectorPolynomialDerivative_zero_outside g e b c hx, fischerInner_zero_left]
  have hB : Integrable B := by
    apply integrable_local_supported hΩ c hcompact hsupp B
      (hρ.mul (ContDiffOn.sum (fun i _ => ContDiffOn.sum (fun j _ =>
        contDiffOn_tensor_fischer_right hΩ h hK e he _ (he i) _ d c z hc.contDiffOn hz.contDiffOn i j))))
    intro x hx
    simp [B, finitePolynomialField_zero_outside _ c hx, fischerInner_zero_left]
  have hW : Integrable W := by
    simp only [W, Finset.mul_sum]
    apply integrable_finsetSum
    intro i _
    apply integrable_finsetSum
    intro j _
    have hw : ContDiffOn ℝ ∞ (fun x => k*fderiv ℝ f x (e x i)) Ω :=
      contDiffOn_const.mul ((hf.fderiv_of_isOpen hΩ (by simp)).clm_apply (he i))
    have hh := integrable_weighted_fischerPair_local hΩ (fun x => ρ x * (k*fderiv ℝ f x (e x i)))
      (hρ.mul hw) (fun t => b t j) (fun t => d t i j) c z hc.contDiffOn hz.contDiffOn hcompact hsupp
    simpa only [mul_assoc] using hh
  have hab : (∫ x, A x) = -(∫ x, B x) :=
    compact_contracted_tensor_fischer_adjoint hΩ h hK e he hframe b d c z hc hz hcompact hsupp
  have hl : (fun x => ρ x * ∑ i, ∑ j, fischerInner
      (weightedCovectorPolynomialDerivative g e b c f k s x (e x i) j)
      (finitePolynomialField (fun t => d t i j) z x)) = fun x => s*A x + W x := by
    funext x
    simp only [weightedCovectorPolynomialDerivative, fischerInner_add_left,
      fischerInner_C_mul_left, A, W, Finset.sum_add_distrib, mul_add, Finset.mul_sum]
    apply congrArg₂ (· + ·) <;> apply Finset.sum_congr rfl <;> intro _ _ <;> apply Finset.sum_congr rfl <;> intro _ _ <;> ring
  have hr : (fun x => ρ x * ∑ i, ∑ j, fischerInner
      (finitePolynomialField (fun t => b t j) c x)
      (weightedTensorPolynomialDerivative g e d z f k (-s) x (e x i) i j)) = fun x => (-s)*B x + W x := by
    funext x
    simp only [weightedTensorPolynomialDerivative, fischerInner_add_right,
      fischerInner_C_mul_right, B, W, Finset.sum_add_distrib, mul_add, Finset.mul_sum]
    apply congrArg₂ (· + ·) <;> apply Finset.sum_congr rfl <;> intro _ _ <;> apply Finset.sum_congr rfl <;> intro _ _ <;> ring
  change (∫ x, ρ x * _) = ∫ x, ρ x * _
  rw [hl, hr, integral_add (hA.const_mul s) hW, integral_add (hB.const_mul (-s)) hW,
    integral_const_mul, integral_const_mul, hab]
  ring

end CalderonN
