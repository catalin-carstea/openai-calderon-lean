module

public import Proof.CalderonN.MovingPolynomial
public import Proof.CalderonN.FischerFields
public import Proof.CalderonN.PolynomialDirectional
import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.Tactic

@[expose] public section

/- Port of EvaluatedFields.lean from the checked Proposition 5.3 release f308cb9d. -/
noncomputable section
open Set Filter MeasureTheory MvPolynomial
open scoped ContDiff Topology
namespace CalderonN
variable {n : ℕ}
variable [NeZero n]

open Set MvPolynomial

open OAI.AnisotropicCalderon.AngularPolynomial

def polynomialConnectionLinear (A : (I n) → (I n) → ℝ) : MvPolynomial (I n) ℝ →ₗ[ℝ] MvPolynomial (I n) ℝ where
  toFun := polynomialConnectionAction A
  map_add' p q := by
    simp only [polynomialConnectionAction, map_add, mul_add, Finset.sum_add_distrib]
  map_smul' a p := by
    simp only [polynomialConnectionAction, smul_eq_C_mul, pderiv_C_mul, Finset.mul_sum, RingHom.id_apply]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring

variable {ι : Type*} [Fintype ι]

lemma polynomialConnectionAction_finite (A : (I n) → (I n) → ℝ) (b : ι → MvPolynomial (I n) ℝ)
    (c : (X n) → ι → ℝ) (y : (X n)) :
    polynomialConnectionAction A (finitePolynomialField b c y) =
      ∑ t, c y t • polynomialConnectionAction A (b t) := by
  change polynomialConnectionLinear A (∑ t, c y t • b t) = _
  simp only [map_sum, map_smul]
  rfl

def evaluatedPolynomialField (g : (MetricField n)) (e : (Frame n)) (b : ι → MvPolynomial (I n) ℝ)
    (c : (X n) → ι → ℝ) (z : (X n) × (X n)) : ℝ :=
  movingFramePolynomial g e (finitePolynomialField b c z.1) z

lemma evaluatedPolynomialField_sum (g : (MetricField n)) (e : (Frame n)) (b : ι → MvPolynomial (I n) ℝ)
    (c : (X n) → ι → ℝ) : evaluatedPolynomialField g e b c =
      fun z => ∑ t, c z.1 t * movingFramePolynomial g e (b t) z := by
  funext z
  simp only [evaluatedPolynomialField, movingFramePolynomial, finitePolynomialField,
    smul_eq_C_mul, map_sum, map_mul, eval_C]

lemma contDiffAt_evaluatedPolynomialField {Ω : Set (X n)} (hΩ : IsOpen Ω) {K : ℝ} {g : (MetricField n)}
    (h : Elliptic Ω K g) (e : (Frame n)) (he : ∀ i, ContDiffOn ℝ ∞ (fun x => e x i) Ω)
    (b : ι → MvPolynomial (I n) ℝ) (c : (X n) → ι → ℝ) {y : (X n)} (hy : y ∈ Ω)
    (hc : ContDiffAt ℝ ∞ c y) (w : (X n)) : ContDiffAt ℝ ∞ (evaluatedPolynomialField g e b c) (y,w) := by
  rw [evaluatedPolynomialField_sum]
  have hct (t : ι) : ContDiffAt ℝ ∞ (fun x => c x t) y := contDiffAt_pi.mp hc t
  have hct' (t : ι) : ContDiffAt ℝ ∞ (fun z : (X n) × (X n) => c z.1 t) (y,w) :=
    (hct t).comp (y,w) contDiffAt_fst
  exact ContDiffAt.sum (fun t _ =>
    (hct' t).mul
      (contDiffAt_movingFramePolynomial hΩ h e he hy w (b t)))

/-- A finite coefficient field differentiated horizontally is its polynomial covariant
    derivative evaluated in the same moving orthonormal frame. -/
theorem evaluatedPolynomialField_horizontal {Ω : Set (X n)} (hΩ : IsOpen Ω) {K : ℝ} {g : (MetricField n)}
    (h : Elliptic Ω K g) (hK : 0 < K) (e : (Frame n))
    (he : ∀ i, ContDiffOn ℝ ∞ (fun x => e x i) Ω)
    (hframe : ∀ x ∈ Ω, ∀ i j, metricPair g x (e x i) (e x j) = if i = j then 1 else 0)
    (b : ι → MvPolynomial (I n) ℝ) (c : (X n) → ι → ℝ) {y : (X n)} (hy : y ∈ Ω)
    (hc : DifferentiableAt ℝ c y) (w a : (X n)) :
    horizontal g (evaluatedPolynomialField g e b c) y w a =
      movingFramePolynomial g e (covariantPolynomialDerivative g e b c y a) (y,w) := by
  have hbase := hc.hasFDerivAt.comp (y,w) (hasFDerivAt_fst (𝕜 := ℝ) (p := (y,w)))
  have hcoef (t : ι) := (ContinuousLinearMap.proj t : (ι → ℝ) →L[ℝ] ℝ).hasFDerivAt.comp (y,w) hbase
  have hpoly (t : ι) := ((contDiffAt_movingFramePolynomial hΩ h e he hy w (b t)).differentiableAt (by simp)).hasFDerivAt
  have hh := HasFDerivAt.sum (u := Finset.univ) (fun t _ => (hcoef t).mul (hpoly t))
  have hfun : evaluatedPolynomialField g e b c =
      ∑ t, ((ContinuousLinearMap.proj t : (ι → ℝ) →L[ℝ] ℝ) ∘ c ∘ Prod.fst) * movingFramePolynomial g e (b t) := by
    funext z
    simp [evaluatedPolynomialField_sum]
  rw [horizontal, hfun, hh.fderiv]
  simp only [_root_.sum_apply, _root_.add_apply, _root_.smul_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.proj_apply, ContinuousLinearMap.coe_fst', smul_eq_mul]
  have hp (t : ι) := movingFramePolynomial_horizontal hΩ h hK e he hframe hy w a (b t)
  unfold horizontal at hp
  simp_rw [hp]
  rw [covariantPolynomialDerivative, polynomialConnectionAction_finite]
  simp only [finitePolynomialFieldDerivative,
    movingFramePolynomial, finitePolynomialField, smul_eq_C_mul, map_add, map_sum, map_mul, eval_C,
    Finset.sum_add_distrib, Function.comp_apply, ContinuousLinearMap.proj_apply, mul_comm, add_comm]

lemma movingFrameCoordinate_frameVector (g : (MetricField n)) (e : (Frame n)) (y : (X n))
    (hframe : ∀ i j, metricPair g y (e y i) (e y j) = if i = j then 1 else 0)
    (v : (I n) → ℝ) (i : (I n)) :
    movingFrameCoordinate g e i (y, ∑ j, v j • e y j) = v i := by
  simp [movingFrameCoordinate, metricPair_sum_left, metricPair_smul_left, hframe]

lemma movingFramePolynomial_injective (g : (MetricField n)) (e : (Frame n)) (y : (X n))
    (hframe : ∀ i j, metricPair g y (e y i) (e y j) = if i = j then 1 else 0)
    (p q : MvPolynomial (I n) ℝ)
    (hpq : ∀ w, movingFramePolynomial g e p (y,w) = movingFramePolynomial g e q (y,w)) : p = q := by
  apply MvPolynomial.funext
  intro v
  simpa only [movingFramePolynomial, movingFrameCoordinate_frameVector g e y hframe] using
    hpq (∑ j, v j • e y j)

end CalderonN
