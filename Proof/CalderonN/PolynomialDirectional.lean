module

public import Proof.CalderonN.PolynomialDerivativeFields
import Mathlib.Tactic

@[expose] public section

/- Port of PolynomialDirectional.lean from the checked Proposition 5.3 release f308cb9d. -/
noncomputable section
open Set Filter MeasureTheory MvPolynomial
open scoped ContDiff Topology
namespace CalderonN
variable {n : ℕ}

open Set MvPolynomial

open OAI.AnisotropicCalderon.AngularPolynomial

/-- Dependence of a frame connection coefficient on its spatial direction. -/
def frameConnectionLinear (g : (MetricField n)) (e : (Frame n)) (y : (X n)) (i j : (I n)) : (X n) →L[ℝ] ℝ :=
  ((metricBilinear g y).flip (e y j)).comp
    (fderiv ℝ (fun x => e x i) y + (connectionBilinear g y).flip (e y i))

lemma frameConnectionLinear_apply (g : (MetricField n)) (e : (Frame n)) (y a : (X n)) (i j : (I n)) :
    frameConnectionLinear g e y i j a = frameConnectionCoefficient g e y a i j := by
  simp [frameConnectionLinear, frameConnectionCoefficient, covariantFrameVector,
    metricBilinear_apply, connectionBilinear_apply]
  simp only [← metricBilinear_apply, map_add, _root_.add_apply]

variable {ι : Type*} [Fintype ι]

/-- Covariant differentiation is linear in its tangent direction. The polynomial target uses
    its ordinary algebraic module structure. -/
def covariantPolynomialLinear (g : (MetricField n)) (e : (Frame n))
    (b : ι → MvPolynomial (I n) ℝ) (c : (X n) → ι → ℝ) (y : (X n)) : (X n) →ₗ[ℝ] MvPolynomial (I n) ℝ :=
  (∑ t, (((ContinuousLinearMap.proj t).comp (fderiv ℝ c y)).toLinearMap).smulRight (b t)) +
    ∑ i, ∑ j, (-(frameConnectionLinear g e y i j).toLinearMap).smulRight
      (MvPolynomial.X i * pderiv j (finitePolynomialField b c y))

lemma covariantPolynomialLinear_apply (g : (MetricField n)) (e : (Frame n))
    (b : ι → MvPolynomial (I n) ℝ) (c : (X n) → ι → ℝ) (y a : (X n)) :
    covariantPolynomialLinear g e b c y a = covariantPolynomialDerivative g e b c y a := by
  simp only [covariantPolynomialLinear, LinearMap.add_apply, LinearMap.sum_apply, LinearMap.smulRight_apply,
    LinearMap.neg_apply, ContinuousLinearMap.coe_coe, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.proj_apply, frameConnectionLinear_apply, smul_eq_C_mul,
    covariantPolynomialDerivative, finitePolynomialFieldDerivative, polynomialConnectionAction]

lemma covariantPolynomialDerivative_direction_sum (g : (MetricField n)) (e : (Frame n))
    (b : ι → MvPolynomial (I n) ℝ) (c : (X n) → ι → ℝ) (y : (X n)) (u : (I n) → (X n)) (a : (I n) → ℝ) :
    covariantPolynomialDerivative g e b c y (∑ i, a i • u i) =
      ∑ i, a i • covariantPolynomialDerivative g e b c y (u i) := by
  simp_rw [← covariantPolynomialLinear_apply, map_sum, map_smul]

end CalderonN
