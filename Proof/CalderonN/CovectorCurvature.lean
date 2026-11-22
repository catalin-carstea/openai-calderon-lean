module

public import Proof.CalderonN.WeightedHessian
public import Proof.CalderonN.PolynomialSlots
public import Proof.CalderonN.WeightedEnergy
import Mathlib.Tactic

@[expose] public section

/- Port of CovectorCurvature.lean from the checked Proposition 5.3 release f308cb9d. -/
noncomputable section
open Set Filter MeasureTheory MvPolynomial
open scoped ContDiff Topology
namespace CalderonN
variable {n : ℕ}
variable [NeZero n]

open Set MvPolynomial

open OAI.AnisotropicCalderon.AngularPolynomial

def covectorCurvatureAction (g : (MetricField n)) (e : (Frame n)) (y a b : (X n))
    (W : (I n) → MvPolynomial (I n) ℝ) (l : (I n)) : MvPolynomial (I n) ℝ :=
  curvaturePolynomialAction g e y a b (W l) -
    ∑ j, C (frameCurvatureCoefficient g e y a b l j) * W j

lemma covectorCurvatureAction_partial (g : (MetricField n)) (e : (Frame n)) (y a b : (X n))
    (p : MvPolynomial (I n) ℝ) (l : (I n)) :
    covectorCurvatureAction g e y a b (fun j => pderiv j p) l =
      pderiv l (curvaturePolynomialAction g e y a b p) := by
  have hh := polynomialConnection_partial_commutator (frameCurvatureCoefficient g e y a b) p l
  simp only [covectorCurvatureAction, curvaturePolynomialAction]
  linear_combination hh

variable {ι : Type*} [Fintype ι]

def weightedCovectorPolynomialDerivative (g : (MetricField n)) (e : (Frame n))
    (b : ι → (I n) → MvPolynomial (I n) ℝ) (c : (X n) → ι → ℝ) (f : (X n) → ℝ) (k s : ℝ)
    (y a : (X n)) (i : (I n)) : MvPolynomial (I n) ℝ :=
  C s * covectorPolynomialDerivative g e b c y a i +
    C (k*fderiv ℝ f y a) * finitePolynomialField (fun t => b t i) c y

lemma weightedCovectorPolynomialDerivative_partial (g : (MetricField n)) (e : (Frame n))
    (b : ι → MvPolynomial (I n) ℝ) (c : (X n) → ι → ℝ) (f : (X n) → ℝ) (k s : ℝ) (y a : (X n)) (i : (I n)) :
    weightedCovectorPolynomialDerivative g e (fun t j => pderiv j (b t)) c f k s y a i =
      pderiv i (weightedPolynomialDerivative g e b c f k s y a) := by
  simp only [weightedCovectorPolynomialDerivative, weightedPolynomialDerivative,
    covectorPolynomialDerivative_partial, finitePolynomialField_partial, map_add, pderiv_C_mul]

def weightedLoweredIndexedHessian (g : (MetricField n)) (e : (Frame n))
    (b : ι → MvPolynomial (I n) ℝ) (c : (X n) → ι → ℝ) (f : (X n) → ℝ) (k s t : ℝ) (y : (X n)) (i j l : (I n)) :
    MvPolynomial (I n) ℝ :=
  weightedCovectorPolynomialDerivative g e (fun a h => pderiv h (weightedDerivativePolynomialFamily b a))
    (weightedDerivativeCoefficientFamily g e c f k t (fun x => e x j)) f k s y (e y i) l -
    C s * ∑ a, C (frameConnectionCoefficient g e y (e y i) j a) *
      weightedCovectorPolynomialDerivative g e (fun a h => pderiv h (b a)) c f k t y (e y a) l

lemma weightedLoweredIndexedHessian_eq_partial (g : (MetricField n)) (e : (Frame n))
    (b : ι → MvPolynomial (I n) ℝ) (c : (X n) → ι → ℝ) (f : (X n) → ℝ) (k s t : ℝ) (y : (X n)) (i j l : (I n)) :
    weightedLoweredIndexedHessian g e b c f k s t y i j l =
      pderiv l (weightedIndexedPolynomialHessian g e b c f k s t y i j) := by
  simp only [weightedLoweredIndexedHessian, weightedCovectorPolynomialDerivative_partial,
    weightedIndexedPolynomialHessian, map_sub, map_sum, pderiv_C_mul]

theorem weightedLoweredIndexedHessian_mixed_commutator {Ω : Set (X n)} (hΩ : IsOpen Ω) {K : ℝ}
    {g : (MetricField n)} (h : Elliptic Ω K g) (hK : 0 < K) (e : (Frame n))
    (he : ∀ i, ContDiffOn ℝ ∞ (fun x => e x i) Ω)
    (hframe : ∀ x ∈ Ω, ∀ i j, metricPair g x (e x i) (e x j) = if i = j then 1 else 0)
    (b : ι → MvPolynomial (I n) ℝ) (c : (X n) → ι → ℝ) (f : (X n) → ℝ) (k : ℝ)
    (hc : ContDiffOn ℝ ∞ c Ω) (hf : ContDiffOn ℝ ∞ f Ω) {y : (X n)} (hy : y ∈ Ω) (i j l : (I n)) :
    weightedLoweredIndexedHessian g e b c f k (-1) 1 y j i l -
      weightedLoweredIndexedHessian g e b c f k 1 (-1) y i j l =
      covectorCurvatureAction g e y (e y i) (e y j) (fun a => pderiv a (finitePolynomialField b c y)) l -
      C (2*k*hessianBilinear g f y (e y i) (e y j)) * pderiv l (finitePolynomialField b c y) := by
  rw [weightedLoweredIndexedHessian_eq_partial, weightedLoweredIndexedHessian_eq_partial, ← map_sub,
    weightedIndexedPolynomialHessian_mixed_commutator hΩ h hK e he hframe b c f k hc hf hy]
  simp only [map_sub, pderiv_C_mul, covectorCurvatureAction_partial]

lemma weightedPolynomialDerivative_homogeneous {k : ℕ} (hk : 1 ≤ k)
    (g : (MetricField n)) (e : (Frame n)) (b : ι → MvPolynomial (I n) ℝ) (hb : ∀ a, (b a).IsHomogeneous k)
    (c : (X n) → ι → ℝ) (f : (X n) → ℝ) (s : ℝ) (y a : (X n)) :
    (weightedPolynomialDerivative g e b c f k s y a).IsHomogeneous k := by
  exact ((covariantPolynomialDerivative_homogeneous hk g e b hb c y a).C_mul s).add
    ((finitePolynomialField_homogeneous b hb c y).C_mul _)

lemma weightedLoweredCross_pointwise_le {k : ℕ} (hk : 1 ≤ k)
    (g : (MetricField n)) (e : (Frame n)) (b : ι → MvPolynomial (I n) ℝ) (hb : ∀ a, (b a).IsHomogeneous k)
    (c : (X n) → ι → ℝ) (f : (X n) → ℝ) (t : ℝ) (y : (X n)) :
    (∑ i, ∑ j, fischerInner
      (weightedCovectorPolynomialDerivative g e (fun a h => pderiv h (b a)) c f k t y (e y i) j)
      (weightedCovectorPolynomialDerivative g e (fun a h => pderiv h (b a)) c f k t y (e y j) i)) ≤
      (k : ℝ) * weightedFrameEnergy g e b c f k t y := by
  simp only [weightedCovectorPolynomialDerivative_partial, weightedFrameEnergy]
  exact sum_fischerInner_pderiv_cross_le _ (fun i => weightedPolynomialDerivative_homogeneous hk g e b hb c f t y (e y i))

end CalderonN
