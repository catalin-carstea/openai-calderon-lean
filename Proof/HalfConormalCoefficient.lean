import Proof.FlatConormalRadialTrace
import Proof.SharpCoefficientMultiplier
import Proof.Archive.NativeHalfCoefficientConormalTrace

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1400000
set_option maxSynthPendingDepth 15
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set MeasureTheory
open scoped ENNReal
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.EnergyBridge OAI.AnisotropicCalderon.DirichletFamily
open OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open OAI.AnisotropicCalderon.SphereHarmonic OAI.AnisotropicCalderon.SpectralCoreRegularity
open OAI.AnisotropicCalderon.NativeHalfCoefficientConormalTrace
open OAI.AnisotropicCalderon.NativeFullHalfRadialTrace

def halfConormalPostL (i : I) : BallSobolev 1 →L[ℝ] SphereSobolev (1/2:ℝ) :=
  -((sphereSobolevLinearCoordinateMulL sphereFischerInner orthogonalSphereHarmonics denseSphereHarmonics
    (1/2:ℝ) (axis i)).comp
      (fixedHalfValueTraceL.comp (TauCeti.Wkp.firstOrderL (mu:=(volume:Measure X)) (Omega:=ballOpens) (p:=2) 0)))

/-- The generic coefficient assembly also constructs the boundary conormal
    flux. The sign in the post-map cancels the divergence assembly's sign. -/
def halfConormalCoefficientL :
    SmoothCoefficientMatrix 2 →L[ℝ] BallSobolev 2 →L[ℝ] SphereSobolev (1/2:ℝ) :=
  (coefficientDivergenceL halfConormalPostL (unitBallCoordinateDerivativeL fixedSobolevCalculus 1)).comp
    (coefficientMatrixMultiplierL fixedSobolevCalculus 0)

theorem halfConormalCoefficientL_eq_native (F : SmoothCoefficientMatrix 2) :
    halfConormalCoefficientL F = nativeHalfCoefficientConormalTraceL sphereFischerInner orthogonalSphereHarmonics
      denseSphereHarmonics fixedSobolevCalculus fixedUnitBallValueTrace F := by
  apply ContinuousLinearMap.ext
  intro U
  simp only [halfConormalCoefficientL,ContinuousLinearMap.comp_apply,coefficientDivergenceL_apply_apply,
    halfConormalPostL,ContinuousLinearMap.neg_apply,coefficientMatrixMultiplierL_apply,
    Finset.sum_neg_distrib,neg_neg,TauCeti.Wkp.firstOrderL_apply,
    nativeHalfCoefficientConormalTraceL_apply]
  rfl

def halfConormalC1Budget : ℝ :=
  2*‖coefficientDivergenceL halfConormalPostL (unitBallCoordinateDerivativeL fixedSobolevCalculus 1)‖

lemma halfConormalC1Budget_nonneg : 0 ≤ halfConormalC1Budget := by
  unfold halfConormalC1Budget
  positivity

/-- Only coefficient values and first derivatives on the actual ball enter
    the H2-to-H1/2 conormal norm bound. -/
theorem norm_halfConormalCoefficientL_local_C1 (F : SmoothCoefficientMatrix 2) (q : ℝ) (hq : 0 ≤ q)
    (hValue : ∀ i j,∀ x ∈ (ballOpens:Set X),|coefficientValue 2 (F i j) x| ≤ q)
    (hDerivative : ∀ i j,∀ x ∈ (ballOpens:Set X),‖fderiv ℝ (coefficientValue 2 (F i j)) x‖ ≤ q) :
    ‖halfConormalCoefficientL F‖ ≤ halfConormalC1Budget*q := by
  have hMatrix : ‖coefficientMatrixMultiplierL fixedSobolevCalculus 0 F‖ ≤ 2*q := by
    apply (pi_norm_le_iff_of_nonneg (by positivity : 0 ≤ 2*q)).2
    intro i
    apply (pi_norm_le_iff_of_nonneg (by positivity : 0 ≤ 2*q)).2
    intro j
    exact norm_coefficientMultiplier_one_le fixedSobolevCalculus (F i j) q hq (hValue i j) (hDerivative i j)
  change ‖coefficientDivergenceL halfConormalPostL (unitBallCoordinateDerivativeL fixedSobolevCalculus 1)
    (coefficientMatrixMultiplierL fixedSobolevCalculus 0 F)‖ ≤ _
  exact ((coefficientDivergenceL halfConormalPostL (unitBallCoordinateDerivativeL fixedSobolevCalculus 1)).le_opNorm _).trans
    ((mul_le_mul_of_nonneg_left hMatrix (norm_nonneg _)).trans_eq (by unfold halfConormalC1Budget;ring))

theorem halfConormalCoefficientL_flat (F0 : SmoothCoefficientMatrix 2) (c : ℝ)
    (hF0 : ∀ x ∈ (ballOpens:Set X),coefficientMatrixField 2 F0 x = 1) :
    halfConormalCoefficientL (c • F0) = c • fixedHalfOutwardTraceL := by
  have hFlat (x : X) (hx : x ∈ (ballOpens:Set X)) : coefficientMatrixField 2 (c • F0) x = c • (1:Mat) := by
    rw [coefficientMatrixField_smul,hF0 x hx]
  let Z := sphereSobolevZeroEquiv orthogonalSphereHarmonics denseSphereHarmonics
  let I0 := sphereSobolevInclusionL (1/2:ℝ) 0 (by norm_num)
  apply ContinuousLinearMap.ext
  intro U
  apply sphereSobolevInclusionL_injective (1/2:ℝ) 0 (by norm_num)
  have hL := congrArg (fun T : BallSobolev 2 →L[ℝ] SphereSobolev (1/2:ℝ) => I0 (T U))
    (halfConormalCoefficientL_eq_native (c • F0))
  have hN := sphereSobolevInclusionL_nativeHalfCoefficientConormalTraceL sphereFischerInner
    orthogonalSphereHarmonics denseSphereHarmonics fixedSobolevCalculus fixedUnitBallValueTrace (c • F0) U
  have hC := congrArg Z (ordinaryConormalTraceL_flat (c • F0) c hFlat U)
  have hLeft := hL.trans (hN.trans (hC.trans (Z.map_smul c _)))
  have hR := sphereSobolevInclusionL_nativeHalfOutwardTraceL sphereFischerInner orthogonalSphereHarmonics
    denseSphereHarmonics fixedSobolevCalculus fixedUnitBallValueTrace U
  have hRight := (I0.map_smul c (fixedHalfOutwardTraceL U)).trans
    (congrArg (fun z : SphereSobolev 0 => c • z) hR)
  exact hLeft.trans hRight.symm

end ShrinkingSpheres
