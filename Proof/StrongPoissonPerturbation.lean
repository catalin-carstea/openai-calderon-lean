import Proof.NativeBoundaryCalculus
import Proof.Archive.NativeH2AffineStrongKernel
import Proof.FlatFullCoefficientOperator

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxSynthPendingDepth 15
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set MeasureTheory
open scoped ENNReal
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.EnergyBridge OAI.AnisotropicCalderon.DirichletFamily
open OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open OAI.AnisotropicCalderon.SphereHarmonic OAI.AnisotropicCalderon.SpectralCoreRegularity

def fixedStrongH2InclusionL : StrongDirichletSpace 0 →L[ℝ] BallSobolev 2 :=
  (strongDirichletSubmodule 0).toSubmodule.subtypeL

/-- The completed actual Poisson solution is the Euclidean lift minus its
    genuine strong Dirichlet correction. -/
def strongPoissonL (F : SmoothCoefficientMatrix 2) : SphereSobolev (3/2:ℝ) →L[ℝ] BallSobolev 2 :=
  nativeH2AffineCorrectionL fixedStrongH2InclusionL
    (strongDirichletOperator fixedSobolevCalculus 0 F).inverse
    (fullCoefficientOperatorL fixedSobolevCalculus 0 F) fixedHarmonicLiftL

lemma strongPoissonL_apply (F : SmoothCoefficientMatrix 2) (f : SphereSobolev (3/2:ℝ)) :
    strongPoissonL F f = fixedHarmonicLiftL f-
      ((strongDirichletOperator fixedSobolevCalculus 0 F).inverse
        (fullCoefficientOperatorL fixedSobolevCalculus 0 F (fixedHarmonicLiftL f)) : BallSobolev 2) := rfl

theorem fullCoefficientOperator_strongPoissonL (F : SmoothCoefficientMatrix 2)
    (hInv : (strongDirichletOperator fixedSobolevCalculus 0 F).IsInvertible)
    (f : SphereSobolev (3/2:ℝ)) :
    fullCoefficientOperatorL fixedSobolevCalculus 0 F (strongPoissonL F f) = 0 := by
  apply nativeH2AffineCorrection_strong_kernel
  intro g
  change ((fullCoefficientOperatorL fixedSobolevCalculus 0 F).comp
    (strongDirichletSubmodule 0).toSubmodule.subtypeL)
    ((strongDirichletOperator fixedSobolevCalculus 0 F).inverse g) = g
  rw [fullCoefficientOperatorL_comp_subtype]
  exact hInv.self_apply_inverse g

theorem strongPoissonL_zero_boundary_difference (F : SmoothCoefficientMatrix 2)
    (f : SphereSobolev (3/2:ℝ)) :
    TauCeti.Wkp.firstOrder 1 (fixedHarmonicLiftL f)-
      TauCeti.Wkp.firstOrder 1 (strongPoissonL F f) ∈
      TauCeti.w1p0Submodule (volume:Measure X) ballOpens 2 := by
  exact nativeH2AffineCorrection_zero_difference fixedStrongH2InclusionL
    (strongDirichletOperator fixedSobolevCalculus 0 F).inverse
    (fullCoefficientOperatorL fixedSobolevCalculus 0 F) fixedHarmonicLiftL (fun _ => rfl) f

/-- Uniform local C1 perturbations give a genuine H3/2-boundary-to-H2 Poisson
    correction estimate for the completed operators. -/
theorem norm_strongPoissonL_sub_flat_le (F F0 : SmoothCoefficientMatrix 2)
    (c C q : ℝ) (hC : 0 ≤ C) (hq : 0 ≤ q)
    (hF0 : ∀ x ∈ (ballOpens : Set X),coefficientMatrixField 2 F0 x = 1)
    (hInvNorm : ‖(strongDirichletOperator fixedSobolevCalculus 0 F).inverse‖ ≤ C)
    (hValue : ∀ i j,∀ x ∈ (ballOpens : Set X),|coefficientValue 2 ((F-c • F0) i j) x| ≤ q)
    (hDerivative : ∀ i j,∀ x ∈ (ballOpens : Set X),‖fderiv ℝ (coefficientValue 2 ((F-c • F0) i j)) x‖ ≤ q) :
    ‖strongPoissonL F-fixedHarmonicLiftL‖ ≤
      C*fullC1OperatorBudget fixedSobolevCalculus*q*‖fixedHarmonicLiftL‖ := by
  have hB := fullC1OperatorBudget_nonneg fixedSobolevCalculus
  have hOp := norm_fullCoefficientOperator_zero_le fixedSobolevCalculus (F-c • F0) q hq hValue hDerivative
  have hSP (f : SphereSobolev (3/2:ℝ)) :
      fullCoefficientOperatorL fixedSobolevCalculus 0 F (fixedHarmonicLiftL f) =
      fullCoefficientOperatorL fixedSobolevCalculus 0 (F-c • F0) (fixedHarmonicLiftL f) := by
    rw [map_sub,_root_.sub_apply]
    have hFlat : fullCoefficientOperatorL fixedSobolevCalculus 0 (c • F0) (fixedHarmonicLiftL f) = 0 :=
      fullCoefficientOperator_flat_harmonicLift fixedSobolevCalculus
        sphereFischerInner orthogonalSphereHarmonics F0 hF0 c f
    rw [hFlat,sub_zero]
  apply ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg (mul_nonneg (mul_nonneg hC hB) hq) (norm_nonneg _))
  intro f
  change ‖strongPoissonL F f-fixedHarmonicLiftL f‖ ≤ _
  rw [strongPoissonL_apply]
  have hCancel : fixedHarmonicLiftL f-
      ((strongDirichletOperator fixedSobolevCalculus 0 F).inverse
        (fullCoefficientOperatorL fixedSobolevCalculus 0 F (fixedHarmonicLiftL f)) : BallSobolev 2)-
      fixedHarmonicLiftL f =
      -((strongDirichletOperator fixedSobolevCalculus 0 F).inverse
        (fullCoefficientOperatorL fixedSobolevCalculus 0 F (fixedHarmonicLiftL f)) : BallSobolev 2) := by abel
  rw [hCancel,norm_neg]
  change ‖(strongDirichletOperator fixedSobolevCalculus 0 F).inverse
    (fullCoefficientOperatorL fixedSobolevCalculus 0 F (fixedHarmonicLiftL f))‖ ≤ _
  calc
    _ ≤ ‖(strongDirichletOperator fixedSobolevCalculus 0 F).inverse‖*
        ‖fullCoefficientOperatorL fixedSobolevCalculus 0 F (fixedHarmonicLiftL f)‖ :=
      ContinuousLinearMap.le_opNorm _ _
    _ ≤ C*‖fullCoefficientOperatorL fixedSobolevCalculus 0 F (fixedHarmonicLiftL f)‖ :=
      mul_le_mul_of_nonneg_right hInvNorm (norm_nonneg _)
    _ = C*‖fullCoefficientOperatorL fixedSobolevCalculus 0 (F-c • F0) (fixedHarmonicLiftL f)‖ := by rw [hSP]
    _ ≤ C*((fullC1OperatorBudget fixedSobolevCalculus*q)*‖fixedHarmonicLiftL f‖) :=
      mul_le_mul_of_nonneg_left (((fullCoefficientOperatorL fixedSobolevCalculus 0 (F-c • F0)).le_opNorm _).trans
        (mul_le_mul_of_nonneg_right hOp (norm_nonneg _))) hC
    _ ≤ C*((fullC1OperatorBudget fixedSobolevCalculus*q)*(‖fixedHarmonicLiftL‖*‖f‖)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (fixedHarmonicLiftL.le_opNorm f)
        (mul_nonneg hB hq)) hC
    _ = _ := by ring

/-- The corresponding half-order radial endpoint is bounded by the same local
    perturbation, followed by the fixed native normal trace. -/
theorem norm_halfRadialPoisson_sub_flat_le (F F0 : SmoothCoefficientMatrix 2)
    (c C q : ℝ) (hC : 0 ≤ C) (hq : 0 ≤ q)
    (hF0 : ∀ x ∈ (ballOpens : Set X),coefficientMatrixField 2 F0 x = 1)
    (hInvNorm : ‖(strongDirichletOperator fixedSobolevCalculus 0 F).inverse‖ ≤ C)
    (hValue : ∀ i j,∀ x ∈ (ballOpens : Set X),|coefficientValue 2 ((F-c • F0) i j) x| ≤ q)
    (hDerivative : ∀ i j,∀ x ∈ (ballOpens : Set X),‖fderiv ℝ (coefficientValue 2 ((F-c • F0) i j)) x‖ ≤ q) :
    ‖fixedHalfOutwardTraceL.comp (strongPoissonL F)-fixedHalfOutwardTraceL.comp fixedHarmonicLiftL‖ ≤
      ‖fixedHalfOutwardTraceL‖*(C*fullC1OperatorBudget fixedSobolevCalculus*q*‖fixedHarmonicLiftL‖) := by
  rw [← ContinuousLinearMap.comp_sub]
  exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
    (mul_le_mul_of_nonneg_left (norm_strongPoissonL_sub_flat_le F F0 c C q hC hq hF0 hInvNorm hValue hDerivative)
      (norm_nonneg _))

end ShrinkingSpheres
