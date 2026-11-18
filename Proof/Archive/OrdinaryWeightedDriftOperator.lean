import Proof.Archive.SupportedDriftInverse
import Proof.Archive.CoordinateFluxEnergy
import Proof.Archive.StrongDerivativeValues

set_option autoImplicit false
set_option maxSynthPendingDepth 10
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open MeasureTheory Filter Set
open scoped ContDiff ENNReal InnerProductSpace Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge
attribute [local instance] TauCeti.W1p0.instNormedAddCommGroup
  TauCeti.W1p0.instInnerProductSpace

def ordinaryCoefficientOperatorL (hcalc : FixedSobolevCalculus) (s : ℕ) :
    SmoothCoefficientMatrix (s + 2) →L[ℝ]
      BallSobolev (s + 2) →L[ℝ] BallSobolev s :=
  (coefficientDivergenceL (unitBallCoordinateDerivativeL hcalc s)
    (unitBallCoordinateDerivativeL hcalc (s + 1))).comp
      (coefficientMatrixMultiplierL hcalc s)

def ordinaryPrincipalL (hcalc : FixedSobolevCalculus) (s : ℕ)
    (F : SmoothCoefficientMatrix (s + 2)) :
    BallSobolev (s + 2) →L[ℝ] BallSobolev s :=
  ordinaryCoefficientOperatorL hcalc s F

theorem ordinaryPrincipalL_apply (hcalc : FixedSobolevCalculus) (s : ℕ)
    (F : SmoothCoefficientMatrix (s + 2)) (E : BallSobolev (s + 2)) :
    ordinaryPrincipalL hcalc s F E = -∑ i : Fin 3, ∑ j : Fin 3,
      unitBallCoordinateDerivativeL hcalc s i
        (coefficientMultiplier hcalc (s + 1) (F i j)
          (unitBallCoordinateDerivativeL hcalc (s + 1) j E)) :=
  coefficientDivergenceL_apply_apply _ _ _ E

theorem ordinaryPrincipalL_restriction (hcalc : FixedSobolevCalculus) (s : ℕ)
    (F : SmoothCoefficientMatrix (s + 2)) :
    (ordinaryPrincipalL hcalc s F).comp
      (strongDirichletSubmodule s).toSubmodule.subtypeL =
        strongDirichletOperator hcalc s F := by
  apply ContinuousLinearMap.ext
  intro U
  simp only [ordinaryPrincipalL, ordinaryCoefficientOperatorL,
    strongDirichletOperator, strongCoefficientOperatorL, unitBallDivergenceL,
    coefficientDivergenceL, operatorMatrixEntryL,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.neg_apply,
    ContinuousLinearMap.sum_apply, ContinuousLinearMap.flip_apply,
    ContinuousLinearMap.compL_apply, ContinuousLinearMap.proj_apply]

theorem ordinaryCoefficientFlux_value_ae (hcalc : FixedSobolevCalculus) (s : ℕ)
    (F : SmoothCoefficientMatrix (s + 2)) (i j : Fin 3)
    (E : BallSobolev (s + 2)) :
    TauCeti.Wkp.value (mu := (volume : Measure R3)) (Omega := ballOpens) (p := 2)
      (s + 1) (coefficientMultiplier hcalc (s + 1) (F i j)
        (unitBallCoordinateDerivativeL hcalc (s + 1) j E))
      =ᵐ[((volume : Measure R3).restrict ballOpens)]
      fun z => coefficientValue (s + 2) (F i j) z *
        (TauCeti.W1p.gradient (TauCeti.Wkp.firstOrder (s + 1) E) z) j :=
  (coefficientMultiplier_value_ae hcalc (s + 1) (F i j)
    (unitBallCoordinateDerivativeL hcalc (s + 1) j E)).trans
      (EventuallyEq.mul (EventuallyEq.refl _ _)
        (unitBallCoordinateDerivativeL_value_ae hcalc (s + 1) j E))

theorem ordinaryPrincipalL_energy (hcalc : FixedSobolevCalculus) (s : ℕ)
    (F : SmoothCoefficientMatrix (s + 2)) (E : BallSobolev (s + 2))
    (v : BallH1Zero) :
    TauCeti.PDE.dirichletForcing (mu := (volume : Measure R3)) (Omega := ballOpens)
      (TauCeti.Wkp.value (mu := (volume : Measure R3)) (Omega := ballOpens) (p := 2) s
        (ordinaryPrincipalL hcalc s F E)) v =
      TauCeti.PDE.energyFormH1 (mu := (volume : Measure R3)) (Omega := ballOpens)
        (coefficientMatrixField (s + 2) F) 0 0
        (TauCeti.Wkp.firstOrder (s + 1) E) (v : BallH1) := by
  have hforcing : TauCeti.PDE.dirichletForcing
      (TauCeti.Wkp.value (mu := (volume : Measure R3)) (Omega := ballOpens) (p := 2) s
        (ordinaryPrincipalL hcalc s F E)) v =
      ∑ i : Fin 3, ∑ j : Fin 3,
        ⟪TauCeti.Wkp.value (mu := (volume : Measure R3)) (Omega := ballOpens) (p := 2)
          (s + 1) (coefficientMultiplier hcalc (s + 1) (F i j)
            (unitBallCoordinateDerivativeL hcalc (s + 1) j E)),
          unitBallCoordinateGradientL i (v : BallH1)⟫_ℝ := by
    rw [TauCeti.PDE.dirichletForcing_apply, ordinaryPrincipalL_apply]
    change ⟪TauCeti.Wkp.valueL (mu := (volume : Measure R3))
      (Omega := ballOpens) (p := 2) s (-∑ i : Fin 3, ∑ j : Fin 3,
        unitBallCoordinateDerivativeL hcalc s i
          (coefficientMultiplier hcalc (s + 1) (F i j)
            (unitBallCoordinateDerivativeL hcalc (s + 1) j E))),
      TauCeti.W1p.value (v : BallH1)⟫_ℝ = _
    simp only [map_neg, map_sum, inner_neg_left, sum_inner, TauCeti.Wkp.valueL_apply]
    simp_rw [unitBallCoordinateDerivative_inner_integration hcalc s]
    simp only [Finset.sum_neg_distrib, neg_neg]
  exact hforcing.trans (energyFormH1_eq_sum_coordinateFlux_inner
    (coefficientMatrixField (s + 2) F) (TauCeti.Wkp.firstOrder (s + 1) E)
    (v : BallH1)
    (fun i j => TauCeti.Wkp.value (mu := (volume : Measure R3))
      (Omega := ballOpens) (p := 2) (s + 1)
        (coefficientMultiplier hcalc (s + 1) (F i j)
          (unitBallCoordinateDerivativeL hcalc (s + 1) j E)))
    (fun i j => ordinaryCoefficientFlux_value_ae hcalc s F i j E)).symm

def ordinaryLowerOrderCoordinateDerivativeL (hcalc : FixedSobolevCalculus)
    (s : ℕ) (i : Fin 3) : BallSobolev (s + 2) →L[ℝ] BallSobolev s :=
  (TauCeti.Wkp.lowerOrderL (mu := (volume : Measure R3)) (Omega := ballOpens)
    (p := 2) s).comp (unitBallCoordinateDerivativeL hcalc (s + 1) i)

theorem ordinaryLowerOrderCoordinateDerivative_value_ae (hcalc : FixedSobolevCalculus)
    (s : ℕ) (i : Fin 3) (E : BallSobolev (s + 2)) :
    TauCeti.Wkp.value (mu := (volume : Measure R3)) (Omega := ballOpens) (p := 2) s
      (ordinaryLowerOrderCoordinateDerivativeL hcalc s i E)
      =ᵐ[((volume : Measure R3).restrict ballOpens)]
      fun z => (TauCeti.W1p.gradient (TauCeti.Wkp.firstOrder (s + 1) E) z) i := by
  change TauCeti.Wkp.value (mu := (volume : Measure R3)) (Omega := ballOpens) (p := 2) s
    (TauCeti.Wkp.lowerOrder s (unitBallCoordinateDerivativeL hcalc (s + 1) i E)) =ᵐ[_] _
  rw [← TauCeti.Wkp.value_succ]
  exact unitBallCoordinateDerivativeL_value_ae hcalc (s + 1) i E

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
