import Proof.Archive.NativePolynomialDriftVariation
import Proof.FlatFullCoefficientOperator
import Proof.AffineCoefficientJets

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option maxSynthPendingDepth 15
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter MeasureTheory MvPolynomial
open scoped ENNReal Topology
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.EnergyBridge OAI.AnisotropicCalderon.DirichletFamily
open OAI.AnisotropicCalderon.SphereHarmonic OAI.AnisotropicCalderon.AngularPolynomial

/-- Polynomial representing a covector in the fixed Euclidean normal chart. -/
def covectorPolynomial (L : X →L[ℝ] ℝ) : MvPolynomial I ℝ :=
  ∑ i, C (L (axis i))*MvPolynomial.X i

lemma eval_covectorPolynomial (L : X →L[ℝ] ℝ) (x : X) :
    eval (polynomialCoordinateMap x) (covectorPolynomial L) = L x := by
  simp only [covectorPolynomial,MvPolynomial.eval_sum,MvPolynomial.eval_mul,eval_C,eval_X,polynomialCoordinateMap_apply]
  conv_rhs => rw [linear_axis_expansion L x]
  apply Finset.sum_congr rfl
  intro i _
  ring

lemma pderiv_covectorPolynomial (L : X →L[ℝ] ℝ) (i : I) :
    pderiv i (covectorPolynomial L) = C (L (axis i)) := by
  simp [covectorPolynomial,pderiv_mul,pderiv_X,Pi.single_apply,mul_ite]

/-- Exact native Sobolev multiplication by a locally polynomial coefficient. -/
theorem coefficientMultiplier_polynomial_on_ball (hcalc : FixedSobolevCalculus) (k : ℕ)
    (F : SmoothCoefficientJets (k+1)) (q p : MvPolynomial I ℝ)
    (hF : ∀ x ∈ (ballOpens : Set X),coefficientValue (k+1) F x = eval (polynomialCoordinateMap x) q) :
    coefficientMultiplier hcalc k F (polynomialBallSobolev k p) = polynomialBallSobolev k (q*p) := by
  apply TauCeti.Wkp.ext k
  apply Lp.ext
  filter_upwards [coefficientMultiplier_value_ae hcalc k F (polynomialBallSobolev k p),
    value_polynomialBallSobolev_ae k p,value_polynomialBallSobolev_ae k (q*p),
    ae_restrict_mem ballOpens.isOpen.measurableSet] with x hM hp hqp hx
  rw [hM,hF x hx,hp,hqp,map_mul]
  rfl

lemma covector_polynomial_divergence (L : X →L[ℝ] ℝ) (p : MvPolynomial I ℝ) :
    (∑ i, pderiv i (covectorPolynomial L*pderiv i p)) =
      OAI.AnisotropicCalderon.GreenRadialTrace.driftDerivative (fun i => L (axis i)) p+
        covectorPolynomial L*laplacian p := by
  simp only [pderiv_mul,pderiv_covectorPolynomial,Finset.sum_add_distrib,
    OAI.AnisotropicCalderon.GreenRadialTrace.driftDerivative,laplacian,Finset.mul_sum]

/-- On harmonic polynomials the first scalar affine divergence variation is
    exactly minus the constant directional derivative. -/
theorem fullCoefficientOperator_affine_harmonic_polynomial (hcalc : FixedSobolevCalculus)
    (F1 : SmoothCoefficientMatrix 2) (L : X →L[ℝ] ℝ)
    (hF1 : ∀ x ∈ (ballOpens : Set X),∀ i j,coefficientValue 2 (F1 i j) x = L x*(1:Mat) i j)
    (p : MvPolynomial I ℝ) (hΔ : laplacian p = 0) :
    fullCoefficientOperatorL hcalc 0 F1 (polynomialBallSobolev 2 p) =
      -polynomialBallSobolev 0 (OAI.AnisotropicCalderon.GreenRadialTrace.driftDerivative (fun i => L (axis i)) p) := by
  have hMult (i j : I) : coefficientMultiplier hcalc 1 (F1 i j)
      (polynomialBallSobolev 1 (pderiv j p)) =
      if i=j then polynomialBallSobolev 1 (covectorPolynomial L*pderiv j p) else 0 := by
    by_cases hij : i=j
    · rw [if_pos hij]
      apply coefficientMultiplier_polynomial_on_ball
      intro x hx
      rw [hF1 x hx,Matrix.one_apply,if_pos hij,mul_one,eval_covectorPolynomial]
    · rw [if_neg hij,coefficientMultiplier_eq_const_of_on_ball hcalc 1 (F1 i j) 0]
      · simp
      · intro x hx
        rw [hF1 x hx,Matrix.one_apply,if_neg hij,mul_zero]
  rw [fullCoefficientOperatorL_apply_apply]
  simp_rw [unitBallCoordinateDerivativeL_polynomialBallSobolev hcalc 1,hMult]
  have hSum (i : I) : (∑ j,unitBallCoordinateDerivativeL hcalc 0 i
      (if i=j then polynomialBallSobolev 1 (covectorPolynomial L*pderiv j p) else 0)) =
      polynomialBallSobolev 0 (pderiv i (covectorPolynomial L*pderiv i p)) := by
    rw [Finset.sum_eq_single i]
    · rw [if_pos rfl,unitBallCoordinateDerivativeL_polynomialBallSobolev]
    · intro j _ hji
      rw [if_neg (Ne.symm hji),map_zero]
    · simp
  simp_rw [hSum]
  change -(∑ i,polynomialBallSobolevLinearMap 0 (pderiv i (covectorPolynomial L*pderiv i p))) = _
  rw [← map_sum,covector_polynomial_divergence,hΔ,mul_zero,add_zero]
  rfl

end ShrinkingSpheres
