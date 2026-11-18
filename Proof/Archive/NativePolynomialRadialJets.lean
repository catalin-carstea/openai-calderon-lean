import Proof.Archive.NativePolynomialBallSobolev

set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open Set Metric Filter MeasureTheory MvPolynomial
open scoped ContDiff ENNReal Gradient InnerProductSpace Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.DirichletFamily
open EnergyBridge MetricVolume

def polynomialEuclideanMap : (Fin 3 → ℝ) →L[ℝ] R3 :=
  ∑ i : Fin 3, (ContinuousLinearMap.proj i).smulRight (coordinateVector i)

theorem polynomialEuclideanMap_apply (x : Fin 3 → ℝ) (i : Fin 3) :
    polynomialEuclideanMap x i = x i := by
  classical
  simp [polynomialEuclideanMap,coordinateVector,Pi.single_apply,mul_ite]

theorem polynomialCoordinateMap_polynomialEuclideanMap (x : Fin 3 → ℝ) :
    polynomialCoordinateMap (polynomialEuclideanMap x) = x := by
  funext i
  exact polynomialEuclideanMap_apply x i

theorem polynomialEuclideanMap_polynomialCoordinateMap (x : R3) :
    polynomialEuclideanMap (polynomialCoordinateMap x) = x := by
  ext i
  exact polynomialEuclideanMap_apply (polynomialCoordinateMap x) i

theorem fderiv_polynomialEval_eq_pi (p : MvPolynomial (Fin 3) ℝ) (x v : R3) :
    fderiv ℝ (fun y : R3 => eval (polynomialCoordinateMap y) p) x v =
      fderiv ℝ (fun y : Fin 3 → ℝ => eval y p)
        (polynomialCoordinateMap x) (polynomialCoordinateMap v) := by
  rw [(hasFDerivAt_polynomialEval p x).fderiv,
    (GreenRadialTrace.hasFDerivAt_eval p (polynomialCoordinateMap x)).fderiv,
    ContinuousLinearMap.comp_apply]

def polynomialBallSobolevLinearMap (k : ℕ) :
    MvPolynomial (Fin 3) ℝ →ₗ[ℝ] BallSobolev k where
  toFun := polynomialBallSobolev k
  map_add' := by
    intro p q
    apply TauCeti.Wkp.ext k
    rw [TauCeti.Wkp.value_add]
    apply Lp.ext
    filter_upwards [value_polynomialBallSobolev_ae k (p+q),
      value_polynomialBallSobolev_ae k p,value_polynomialBallSobolev_ae k q,
      Lp.coeFn_add (TauCeti.Wkp.value k (polynomialBallSobolev k p))
        (TauCeti.Wkp.value k (polynomialBallSobolev k q))] with x hsum hp hq hadd
    rw [hsum,hadd,Pi.add_apply,hp,hq,map_add]
  map_smul' := by
    intro c p
    apply TauCeti.Wkp.ext k
    rw [TauCeti.Wkp.value_smul]
    change TauCeti.Wkp.value k (polynomialBallSobolev k (c • p)) =
      c • TauCeti.Wkp.value k (polynomialBallSobolev k p)
    apply Lp.ext
    filter_upwards [value_polynomialBallSobolev_ae k (c • p),
      value_polynomialBallSobolev_ae k p,
      Lp.coeFn_smul c (TauCeti.Wkp.value k (polynomialBallSobolev k p))] with x hcp hp hsmul
    rw [hcp,hsmul,Pi.smul_apply,hp,MvPolynomial.smul_eval]
    rfl


end OAI.AnisotropicCalderon.DirichletFamily
