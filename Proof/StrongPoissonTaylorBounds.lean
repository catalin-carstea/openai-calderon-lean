import Proof.StrongPoissonTaylor
import Proof.OperatorPoissonTaylor

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1400000
set_option maxSynthPendingDepth 15
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.EnergyBridge OAI.AnisotropicCalderon.DirichletFamily
open OAI.AnisotropicCalderon.SphereHarmonic OAI.AnisotropicCalderon.SpectralCoreRegularity

theorem norm_strongFirstPoissonVariationL_le (F0 F1 : SmoothCoefficientMatrix 2) (c C0 P : ℝ)
    (hC0 : 0 ≤ C0) (hP : 0 ≤ P)
    (hInv0 : ‖(strongDirichletOperator fixedSobolevCalculus 0 (c • F0)).inverse‖ ≤ C0)
    (hT1 : ‖fullCoefficientOperatorL fixedSobolevCalculus 0 F1‖ ≤ P) :
    ‖strongFirstPoissonVariationL F0 F1 c‖ ≤ C0*P*‖fixedHarmonicLiftL‖ := by
  have hj : ‖fixedStrongH2InclusionL‖ ≤ 1 := Submodule.norm_subtypeL_le _
  rw [strongFirstPoissonVariationL,norm_neg]
  calc
    _ ≤ ‖fixedStrongH2InclusionL‖*
        (‖(strongDirichletOperator fixedSobolevCalculus 0 (c • F0)).inverse‖*
          (‖fullCoefficientOperatorL fixedSobolevCalculus 0 F1‖*‖fixedHarmonicLiftL‖)) :=
      (ContinuousLinearMap.opNorm_comp_le _ _).trans
        (mul_le_mul_of_nonneg_left ((ContinuousLinearMap.opNorm_comp_le _ _).trans
          (mul_le_mul_of_nonneg_left (ContinuousLinearMap.opNorm_comp_le _ _) (norm_nonneg _))) (norm_nonneg _))
    _ ≤ 1*(C0*(P*‖fixedHarmonicLiftL‖)) := by gcongr
    _ = _ := by ring

/-- The quantitative resolvent estimate controls the bulk solution remainder
    itself, before any radial or conormal trace is applied. -/
theorem norm_strongPoisson_first_remainder_le (F F0 F1 : SmoothCoefficientMatrix 2)
    (c r C C0 D P Q : ℝ) (hr : 0 ≤ r) (hC : 0 ≤ C) (hC0 : 0 ≤ C0)
    (hD : 0 ≤ D) (hP : 0 ≤ P) (hQ : 0 ≤ Q)
    (hF0 : ∀ x ∈ (ballOpens:Set X),coefficientMatrixField 2 F0 x = 1)
    (hInv : (strongDirichletOperator fixedSobolevCalculus 0 F).IsInvertible)
    (hInv0 : (strongDirichletOperator fixedSobolevCalculus 0 (c • F0)).IsInvertible)
    (hNorm : ‖(strongDirichletOperator fixedSobolevCalculus 0 F).inverse‖ ≤ C)
    (hNorm0 : ‖(strongDirichletOperator fixedSobolevCalculus 0 (c • F0)).inverse‖ ≤ C0)
    (hDiff : ‖strongDirichletOperator fixedSobolevCalculus 0 F-
      strongDirichletOperator fixedSobolevCalculus 0 (c • F0)‖ ≤ D*r)
    (hT1 : ‖fullCoefficientOperatorL fixedSobolevCalculus 0 F1‖ ≤ P)
    (hTR : ‖fullCoefficientOperatorL fixedSobolevCalculus 0 F-
      fullCoefficientOperatorL fixedSobolevCalculus 0 (c • F0)-
      r • fullCoefficientOperatorL fixedSobolevCalculus 0 F1‖ ≤ Q*r^2) :
    ‖strongPoissonL F-fixedHarmonicLiftL-r • strongFirstPoissonVariationL F0 F1 c‖ ≤
      C*(Q+C0*D*P)*‖fixedHarmonicLiftL‖*r^2 := by
  let A := strongDirichletOperator fixedSobolevCalculus 0 F
  let A0 := strongDirichletOperator fixedSobolevCalculus 0 (c • F0)
  let T := fullCoefficientOperatorL fixedSobolevCalculus 0 F
  let T0 := fullCoefficientOperatorL fixedSobolevCalculus 0 (c • F0)
  let T1 := fullCoefficientOperatorL fixedSobolevCalculus 0 F1
  have hFlat : T0.comp fixedHarmonicLiftL = 0 := by
    apply ContinuousLinearMap.ext
    intro f
    exact fullCoefficientOperator_flat_harmonicLift fixedSobolevCalculus sphereFischerInner
      orthogonalSphereHarmonics F0 hF0 c f
  have hj : ‖fixedStrongH2InclusionL‖ ≤ 1 := Submodule.norm_subtypeL_le _
  have hb := norm_poisson_first_variation_remainder_le fixedStrongH2InclusionL A A0 T T0 T1 fixedHarmonicLiftL
    hInv hInv0 hFlat hj r C C0 D P Q hr hC hC0 hD hP hQ hNorm hNorm0 hDiff hT1 hTR
  have hPa : fixedHarmonicLiftL-fixedStrongH2InclusionL.comp (A.inverse.comp (T.comp fixedHarmonicLiftL)) =
      strongPoissonL F := by
    apply ContinuousLinearMap.ext
    intro f
    rfl
  have hP1 : -(fixedStrongH2InclusionL.comp (A0.inverse.comp (T1.comp fixedHarmonicLiftL))) =
      strongFirstPoissonVariationL F0 F1 c := rfl
  have hEq := congrArg₂ (fun Pa P1 : SphereSobolev (3/2:ℝ) →L[ℝ] BallSobolev 2 =>
    Pa-fixedHarmonicLiftL-r • P1) hPa hP1
  have hNormEq := congrArg (fun R : SphereSobolev (3/2:ℝ) →L[ℝ] BallSobolev 2 => ‖R‖) hEq
  exact hNormEq ▸ hb

end ShrinkingSpheres
