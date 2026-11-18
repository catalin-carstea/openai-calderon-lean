import Proof.Archive.NativePolynomialRadialJets
import Proof.Archive.OrdinaryWeightedDriftOperator

set_option autoImplicit false
set_option maxSynthPendingDepth 15
noncomputable section
open Set Metric Filter MeasureTheory MvPolynomial
open scoped ContDiff ENNReal Gradient InnerProductSpace Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.DirichletFamily
open EnergyBridge MetricVolume DriftBootstrap

theorem ordinaryLowerOrderCoordinateDerivativeL_polynomialBallSobolev
    (hcalc : FixedSobolevCalculus) (s : ℕ) (i : Fin 3)
    (p : MvPolynomial (Fin 3) ℝ) :
    ordinaryLowerOrderCoordinateDerivativeL hcalc s i (polynomialBallSobolev (s+2) p) =
      polynomialBallSobolev s (pderiv i p) := by
  change TauCeti.Wkp.lowerOrder s
    (unitBallCoordinateDerivativeL hcalc (s+1) i (polynomialBallSobolev (s+2) p)) = _
  rw [unitBallCoordinateDerivativeL_polynomialBallSobolev]
  exact lowerOrder_smoothBallSobolev s (smoothPolynomialData (pderiv i p))

theorem nativePolynomial_drift_operator
    (hcalc : FixedSobolevCalculus) (s : ℕ) (d : R3) (p : MvPolynomial (Fin 3) ℝ) :
    (∑ i : Fin 3, (d i) • ordinaryLowerOrderCoordinateDerivativeL hcalc s i)
      (polynomialBallSobolev (s+2) p) =
        polynomialBallSobolev s (GreenRadialTrace.driftDerivative (polynomialCoordinateMap d) p) := by
  simp only [ContinuousLinearMap.sum_apply,ContinuousLinearMap.smul_apply]
  simp_rw [ordinaryLowerOrderCoordinateDerivativeL_polynomialBallSobolev hcalc s]
  change (∑ i : Fin 3, (d i) • polynomialBallSobolevLinearMap s (pderiv i p)) =
    polynomialBallSobolevLinearMap s (GreenRadialTrace.driftDerivative (polynomialCoordinateMap d) p)
  rw [GreenRadialTrace.driftDerivative,map_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [← MvPolynomial.smul_eq_C_mul,map_smul]
  rfl

theorem polynomialEval_driftFirstVariation_zero_on_sphere
    (k : ℕ) (d : R3) (p : MvPolynomial (Fin 3) ℝ) (z : R3) (hz : ‖z‖ = 1) :
    eval (polynomialCoordinateMap z)
      (GreenRadialTrace.driftFirstVariation k (polynomialCoordinateMap d) p) = 0 := by
  have hs : ∑ i : Fin 3, (polynomialCoordinateMap z i)^2 = 1 := by
    simpa only [polynomialCoordinateMap_apply,hz,one_pow] using
      (EuclideanSpace.real_norm_sq_eq z).symm
  exact GreenRadialTrace.eval_driftFirstVariation_eq_zero k (polynomialCoordinateMap d) p
    (polynomialCoordinateMap z) hs

theorem fderiv_polynomialEval_driftFirstVariation_radial
    (k : ℕ) (hk : 1 ≤ k) (d : R3) (p : MvPolynomial (Fin 3) ℝ)
    (z : R3) (hz : ‖z‖ = 1) :
    fderiv ℝ (fun x : R3 => eval (polynomialCoordinateMap x)
      (GreenRadialTrace.driftFirstVariation k (polynomialCoordinateMap d) p)) z z =
      -(2*(k : ℝ)+1)⁻¹ * fderiv ℝ
        (fun x : R3 => eval (polynomialCoordinateMap x) p) z d := by
  have hs : ∑ i : Fin 3, (polynomialCoordinateMap z i)^2 = 1 := by
    simpa only [polynomialCoordinateMap_apply,hz,one_pow] using
      (EuclideanSpace.real_norm_sq_eq z).symm
  rw [fderiv_polynomialEval_eq_pi,fderiv_polynomialEval_eq_pi]
  exact GreenRadialTrace.fderiv_driftFirstVariation_three_at_sphere hk
    (polynomialCoordinateMap d) p (polynomialCoordinateMap z) hs

end OAI.AnisotropicCalderon.DirichletFamily
