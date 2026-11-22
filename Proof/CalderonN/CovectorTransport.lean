module

public import Proof.CalderonN.PolynomialSlots
public import Proof.CalderonN.FischerAdjoint
public import Proof.CalderonN.CovectorCancellation
import Mathlib.Tactic

@[expose] public section

/- Port of CovectorTransport.lean from the checked Proposition 5.3 release f308cb9d. -/
noncomputable section
open Set Filter MeasureTheory MvPolynomial
open scoped ContDiff Topology
namespace CalderonN
variable {n : ℕ}

open Set MeasureTheory MvPolynomial

open OAI.AnisotropicCalderon.AngularPolynomial

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

def finiteCovectorFischerPair (b : ι → (I n) → MvPolynomial (I n) ℝ) (d : κ → (I n) → MvPolynomial (I n) ℝ)
    (c : (X n) → ι → ℝ) (z : (X n) → κ → ℝ) (x : (X n)) : ℝ :=
  ∑ i, fischerInner (finitePolynomialField (fun t => b t i) c x) (finitePolynomialField (fun t => d t i) z x)

lemma contDiff_finiteCovectorFischerPair (b : ι → (I n) → MvPolynomial (I n) ℝ) (d : κ → (I n) → MvPolynomial (I n) ℝ)
    (c : (X n) → ι → ℝ) (z : (X n) → κ → ℝ) (hc : ContDiff ℝ ∞ c) (hz : ContDiff ℝ ∞ z) :
    ContDiff ℝ ∞ (finiteCovectorFischerPair b d c z) :=
  ContDiff.sum (fun i _ => contDiff_fischerPair (fun t => b t i) (fun t => d t i) c z hc hz)

lemma finiteCovectorFischerPair_tsupport (b : ι → (I n) → MvPolynomial (I n) ℝ) (d : κ → (I n) → MvPolynomial (I n) ℝ)
    (c : (X n) → ι → ℝ) (z : (X n) → κ → ℝ) : tsupport (finiteCovectorFischerPair b d c z) ⊆ tsupport c := by
  apply closure_minimal _ (isClosed_tsupport c)
  intro x hx
  by_contra hout
  have hc0 := image_eq_zero_of_notMem_tsupport hout
  apply hx
  simp [finiteCovectorFischerPair, finitePolynomialField, hc0, fischerInner_zero_left]

lemma fderiv_finiteCovectorFischerPair {Ω : Set (X n)} (hΩ : IsOpen Ω) {K : ℝ}
    {g : (MetricField n)} (h : Elliptic Ω K g) (hK : 0 < K) (e : (Frame n))
    (he : ∀ i, ContDiffOn ℝ ∞ (fun x => e x i) Ω)
    (hframe : ∀ x ∈ Ω, ∀ i j, metricPair g x (e x i) (e x j) = if i = j then 1 else 0)
    (b : ι → (I n) → MvPolynomial (I n) ℝ) (d : κ → (I n) → MvPolynomial (I n) ℝ)
    (c : (X n) → ι → ℝ) (z : (X n) → κ → ℝ) (hc : ContDiff ℝ ∞ c) (hz : ContDiff ℝ ∞ z)
    {y : (X n)} (hy : y ∈ Ω) (a : (X n)) :
    fderiv ℝ (finiteCovectorFischerPair b d c z) y a =
      ∑ i, (fischerInner (covectorPolynomialDerivative g e b c y a i) (finitePolynomialField (fun t => d t i) z y) +
        fischerInner (finitePolynomialField (fun t => b t i) c y) (covectorPolynomialDerivative g e d z y a i)) := by
  have hpart (i : (I n)) := (contDiff_fischerPair (fun t => b t i) (fun t => d t i) c z hc hz).differentiable
    (by simp) y
  have hh := HasFDerivAt.sum (u := Finset.univ) (fun i _ => (hpart i).hasFDerivAt)
  have hfun : finiteCovectorFischerPair b d c z =
      ∑ i, (fun x => fischerInner (finitePolynomialField (fun t => b t i) c x) (finitePolynomialField (fun t => d t i) z x)) := by
    funext x
    simp [finiteCovectorFischerPair]
  rw [hfun, hh.fderiv]
  simp only [_root_.sum_apply]
  simp_rw [covariantPolynomialDerivative_fischer_compatible hΩ h hK e he hframe _ _ c z hy a
    (hc.differentiable (by simp) y) (hz.differentiable (by simp) y)]
  exact (OAI.AnisotropicCalderon.FiniteCovectorTransport.fischer_covector_slot_cancellation
    (fun j i => frameConnectionCoefficient g e y a i j)
    (fun j i => frameConnection_skew hΩ h hK e he hframe hy a i j)
    (fun i => finitePolynomialField (fun t => b t i) c y)
    (fun i => finitePolynomialField (fun t => d t i) z y)
    (fun i => covariantPolynomialDerivative g e (fun t => b t i) c y a)
    (fun i => covariantPolynomialDerivative g e (fun t => d t i) z y a)).symm

/-- Covector index corrections cancel in the contracted integration-by-parts identity. -/
theorem compact_local_covector_fischer_contraction {Ω : Set (X n)} (hΩ : IsOpen Ω) {K : ℝ}
    {g : (MetricField n)} (h : Elliptic Ω K g) (hK : 0 < K) (e : (Frame n))
    (he : ∀ i, ContDiffOn ℝ ∞ (fun x => e x i) Ω)
    (hframe : ∀ x ∈ Ω, ∀ i j, metricPair g x (e x i) (e x j) = if i = j then 1 else 0)
    (ρ : (X n) → ℝ) (hρ : ContDiffOn ℝ ∞ ρ Ω) (V : (X n) → (X n)) (hV : ContDiffOn ℝ ∞ V Ω)
    (b : ι → (I n) → MvPolynomial (I n) ℝ) (d : κ → (I n) → MvPolynomial (I n) ℝ)
    (c : (X n) → ι → ℝ) (z : (X n) → κ → ℝ) (hc : ContDiff ℝ ∞ c) (hz : ContDiff ℝ ∞ z)
    (hcompact : HasCompactSupport c) (hsupp : tsupport c ⊆ Ω) :
    (∫ y, ρ y * ∑ i,
      (fischerInner (covectorPolynomialDerivative g e b c y (V y) i) (finitePolynomialField (fun t => d t i) z y) +
        fischerInner (finitePolynomialField (fun t => b t i) c y) (covectorPolynomialDerivative g e d z y (V y) i))) =
      -(∫ y, weightedDivergence ρ V y * finiteCovectorFischerPair b d c z y) := by
  have ht := finiteCovectorFischerPair_tsupport b d c z
  have hpoint (y : (X n)) :
      fderiv ℝ (finiteCovectorFischerPair b d c z) y (V y) =
        ∑ i, (fischerInner (covectorPolynomialDerivative g e b c y (V y) i) (finitePolynomialField (fun t => d t i) z y) +
          fischerInner (finitePolynomialField (fun t => b t i) c y) (covectorPolynomialDerivative g e d z y (V y) i)) := by
    by_cases hy : y ∈ Ω
    · exact fderiv_finiteCovectorFischerPair hΩ h hK e he hframe b d c z hc hz hy (V y)
    · have hout : y ∉ tsupport c := fun hx => hy (hsupp hx)
      have hpout : y ∉ tsupport (finiteCovectorFischerPair b d c z) := fun hx => hout (ht hx)
      have hc0 := image_eq_zero_of_notMem_tsupport hout
      have hdc0 := fderiv_of_notMem_tsupport (𝕜 := ℝ) hout
      simp [fderiv_of_notMem_tsupport (𝕜 := ℝ) hpout, covectorPolynomialDerivative,
        covariantPolynomialDerivative, finitePolynomialField, finitePolynomialFieldDerivative,
        polynomialConnectionAction, hc0, hdc0, fischerInner_zero_left, fischerInner_zero_right]
  have hh := compact_scalar_local_adjoint hΩ ρ (finiteCovectorFischerPair b d c z) V hρ
    (contDiff_finiteCovectorFischerPair b d c z hc hz) hV
    (hcompact.of_isClosed_subset (isClosed_tsupport _) ht) (ht.trans hsupp)
  simpa only [hpoint] using hh

end CalderonN
