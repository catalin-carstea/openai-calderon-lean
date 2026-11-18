import Proof.FlatFullCoefficientOperator
import Proof.ClassicalWeakDirichlet

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 700000
set_option maxSynthPendingDepth 15
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter MeasureTheory
open scoped ContDiff ENNReal Gradient
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon
open OAI.AnisotropicCalderon.EnergyBridge OAI.AnisotropicCalderon.DirichletFamily
open OAI.AnisotropicCalderon.MetricVolume OAI.AnisotropicCalderon.ConnectionError
open OAI.AnisotropicCalderon.NativeHarmonicLiftTraceCompatibility

/-- Classical Euclidean harmonicity gives the exact native strong kernel,
    using the actual coordinate derivatives of a smooth representative. -/
theorem nativeEuclideanLaplacian_smooth_eq_zero (hcalc : FixedSobolevCalculus)
    (V : SmoothData)
    (hFlat : ∀ x ∈ (ballOpens : Set X),coordinateFluxDivergence (gradient V.1) x = 0) :
    nativeEuclideanLaplacianL hcalc (smoothBallSobolev 2 V) = 0 := by
  have hOp : nativeEuclideanLaplacianL hcalc (smoothBallSobolev 2 V) =
      ∑ i : Fin 3,smoothBallSobolev 0 (smoothCoordinateDerivative (smoothCoordinateDerivative V i) i) := by
    simp only [nativeEuclideanLaplacianL,ContinuousLinearMap.sum_apply,ContinuousLinearMap.comp_apply]
    apply Finset.sum_congr rfl
    intro i hi
    rw [unitBallCoordinateDerivativeL_smoothBallSobolev hcalc 1 i V,
      unitBallCoordinateDerivativeL_smoothBallSobolev hcalc 0 i (smoothCoordinateDerivative V i)]
  have hDiv (x : X) :
      (∑ i : Fin 3,(smoothCoordinateDerivative (smoothCoordinateDerivative V i) i).1 x) =
        coordinateFluxDivergence (gradient V.1) x := by
    unfold coordinateFluxDivergence
    apply Finset.sum_congr rfl
    intro i hi
    rw [show (fun y : X => gradient V.1 y i) =
      (fun y => fderiv ℝ V.1 y (MetricVolume.coordinateVector i)) from
        funext (fun y => gradient_coordinate V.1 y i)]
    rfl
  apply TauCeti.Wkp.ext 0
  rw [hOp,TauCeti.Wkp.value_zero]
  change (TauCeti.Wkp.valueL (mu:=(volume:Measure X)) (Omega:=ballOpens) (p:=2) 0)
    (∑ i : Fin 3,smoothBallSobolev 0 (smoothCoordinateDerivative (smoothCoordinateDerivative V i) i)) = 0
  rw [map_sum]
  change (∑ i : Fin 3,TauCeti.Wkp.value (mu:=(volume:Measure X))
    (Omega:=ballOpens) (p:=2) 0
      (smoothBallSobolev 0 (smoothCoordinateDerivative (smoothCoordinateDerivative V i) i))) = 0
  apply Lp.ext
  filter_upwards [Lp.coeFn_finsetSum Finset.univ (fun i : Fin 3 =>
      TauCeti.Wkp.value (mu:=(volume:Measure X)) (Omega:=ballOpens) (p:=2) 0
        (smoothBallSobolev 0 (smoothCoordinateDerivative (smoothCoordinateDerivative V i) i))),
    ae_all_iff.mpr (fun i : Fin 3 => value_smoothBallSobolev_ae 0
      (smoothCoordinateDerivative (smoothCoordinateDerivative V i) i)),
    Lp.coeFn_zero (ℝ) 2 ((volume:Measure X).restrict ballOpens),
    ae_restrict_mem ballOpens.isOpen.measurableSet] with x hs hx hz hball
  rw [hs,hz]
  simp only [Finset.sum_apply,Pi.zero_apply]
  exact (Finset.sum_congr rfl (fun i hi => hx i)).trans ((hDiv x).trans (hFlat x hball))

end ShrinkingSpheres
