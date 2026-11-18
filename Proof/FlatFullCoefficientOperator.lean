import Proof.FullCoefficientEnergy
import Proof.Archive.NativeHarmonicLiftTraceCompatibility

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 600000
set_option maxSynthPendingDepth 15
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter MeasureTheory
open scoped ENNReal
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.EnergyBridge OAI.AnisotropicCalderon.DirichletFamily
open OAI.AnisotropicCalderon.SphereHarmonic OAI.AnisotropicCalderon.SpectralCoreRegularity
open OAI.AnisotropicCalderon.NativeHarmonicLiftCompletion
open OAI.AnisotropicCalderon.NativeHarmonicLiftTraceCompatibility

lemma coefficientMultiplier_eq_const_of_on_ball (hcalc : FixedSobolevCalculus) (k : ℕ)
    (F : SmoothCoefficientJets (k+1)) (c : ℝ)
    (hF : ∀ x ∈ (ballOpens : Set X),coefficientValue (k+1) F x = c) :
    coefficientMultiplier hcalc k F = c • ContinuousLinearMap.id ℝ (BallSobolev k) := by
  apply ContinuousLinearMap.ext
  intro U
  apply TauCeti.Wkp.ext k
  change TauCeti.Wkp.value k (coefficientMultiplier hcalc k F U) = TauCeti.Wkp.value k (c • U)
  rw [TauCeti.Wkp.value_smul]
  apply Lp.ext
  filter_upwards [coefficientMultiplier_value_ae hcalc k F U,
    Lp.coeFn_smul c (TauCeti.Wkp.value k U),
    ae_restrict_mem ballOpens.isOpen.measurableSet] with x hx hs hball
  rw [hx,hs,hF x hball]
  rfl

/-- A flat representative on the ball gives exactly the Euclidean Laplacian,
    regardless of its compact extension outside the ball. -/
theorem fullCoefficientOperator_flat_eq (hcalc : FixedSobolevCalculus)
    (F0 : SmoothCoefficientMatrix 2)
    (hF0 : ∀ x ∈ (ballOpens : Set X),coefficientMatrixField 2 F0 x = 1) :
    fullCoefficientOperatorL hcalc 0 F0 = -nativeEuclideanLaplacianL hcalc := by
  have hMult (i j : Fin 3) : coefficientMultiplier hcalc 1 (F0 i j) =
      (if i=j then (1:ℝ) else 0) • ContinuousLinearMap.id ℝ (BallSobolev 1) := by
    apply coefficientMultiplier_eq_const_of_on_ball
    intro x hx
    have hh := congrArg (fun A : Mat => A i j) (hF0 x hx)
    simpa only [coefficientMatrixField,Matrix.one_apply] using hh
  apply ContinuousLinearMap.ext
  intro U
  rw [fullCoefficientOperatorL_apply_apply]
  simp [hMult,nativeEuclideanLaplacianL]
  apply Finset.sum_congr rfl
  intro i hi
  calc
    _ = ∑ j : Fin 3,if j=i then
        unitBallCoordinateDerivativeL hcalc 0 i (unitBallCoordinateDerivativeL hcalc 1 i U) else 0 := by
      apply Finset.sum_congr rfl
      intro j hj
      by_cases h : i=j
      · subst j
        simp
      · simp [h,Ne.symm h]
    _ = _ := by simp

/-- The completed Euclidean Poisson lift is killed by every positive scalar
    flat representative used in the actual perturbation argument. -/
theorem fullCoefficientOperator_flat_harmonicLift (hcalc : FixedSobolevCalculus)
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics)
    (F0 : SmoothCoefficientMatrix 2)
    (hF0 : ∀ x ∈ (ballOpens : Set X),coefficientMatrixField 2 F0 x = 1)
    (c : ℝ) (f : SphereSobolev (3/2:ℝ)) :
    fullCoefficientOperatorL hcalc 0 (c • F0) (harmonicLiftCompletion hF f) = 0 := by
  rw [map_smul,ContinuousLinearMap.smul_apply,fullCoefficientOperator_flat_eq hcalc F0 hF0]
  simp only [ContinuousLinearMap.neg_apply,
    nativeEuclideanLaplacianL_harmonicLiftCompletion hcalc hF hO,neg_zero,smul_zero]

end ShrinkingSpheres
