import Proof.ConormalFirstAdjoint
import Proof.OperatorPoissonTaylor

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxSynthPendingDepth 15
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.SphereHarmonic
attribute [local irreducible] sphereSobolevDegreeL

/-- The conormal/normal-inverse expansions imply a quadratic radial adjoint
    remainder on H1. Its first correction is the bounded L2 adjoint, with
    the remaining coefficient action quantified separately by CT. -/
theorem norm_conormal_radial_adjoint_taylor_le
    (N N1 Td : SphereSobolev 1 →L[ℝ] SphereSobolev 0)
    (H M1 : SphereSobolev 1 →L[ℝ] SphereSobolev 1)
    (B : SphereSobolev 0 →L[ℝ] SphereSobolev 0)
    (c r K CN1 CN2 CI CRI CM1 CT : ℝ)
    (hc : 0 < c) (hcK : c ≤ K) (hciK : c⁻¹ ≤ K) (hr : 0 ≤ r) (hr1 : r ≤ 1)
    (hK : 0 ≤ K) (hCN1 : 0 ≤ CN1) (hCN2 : 0 ≤ CN2) (hCI : 0 ≤ CI)
    (hCRI : 0 ≤ CRI) (hCM1 : 0 ≤ CM1) (hCT : 0 ≤ CT)
    (hN1 : ‖N1‖ ≤ CN1) (hM1 : ‖M1‖ ≤ CM1) (hH : ‖H‖ ≤ CI)
    (hNR : ‖N-c • sphereSobolevDegreeL-r • N1‖ ≤ CN2*r^2)
    (hHR : ‖H-c⁻¹ • ContinuousLinearMap.id ℝ (SphereSobolev 1)+r • ((c⁻¹)^2 • M1)‖ ≤ CRI*r^2)
    (hT : ‖Td‖ ≤ CT*r^2)
    (hFirst : c⁻¹ • (N1-sphereSobolevDegreeL.comp M1) =
      B.adjoint.comp (sphereSobolevInclusionL 1 0 (by norm_num))) :
    ‖(N-Td).comp H-sphereSobolevDegreeL-r • B.adjoint.comp (sphereSobolevInclusionL 1 0 (by norm_num))‖ ≤
      ((2*K+CN1+CN2)*CRI+(CN1+CN2)*(K^2*CM1)+CN2*K+CT*CI)*r^2 := by
  let A0 := c • sphereSobolevDegreeL
  let P0 := c⁻¹ • ContinuousLinearMap.id ℝ (SphereSobolev 1)
  let P1 := -((c⁻¹)^2 • M1)
  let D := 2*K+CN1+CN2
  have hb : 0 ≤ c⁻¹ := inv_nonneg.mpr hc.le
  have hD : 0 ≤ D := by dsimp [D];positivity
  have hP1N : 0 ≤ K^2*CM1 := mul_nonneg (sq_nonneg _) hCM1
  have hP0 : ‖P0‖ ≤ K := by
    apply ContinuousLinearMap.opNorm_le_bound _ hK
    intro u
    change ‖c⁻¹ • u‖ ≤ K*‖u‖
    exact (norm_smul_le _ _).trans (by rw [Real.norm_eq_abs,abs_of_nonneg hb];exact mul_le_mul_of_nonneg_right hciK (norm_nonneg _))
  have hP1 : ‖P1‖ ≤ K^2*CM1 := by
    change ‖-((c⁻¹)^2 • M1)‖ ≤ _
    rw [norm_neg,norm_smul,Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
    gcongr
  have hNDiff : ‖N-A0‖ ≤ (CN1+CN2)*r :=
    norm_sub_of_affine_remainder_le N A0 N1 r CN1 CN2 hr hr1 hCN1 hCN2 hN1 hNR
  have hA0 : ‖A0‖ ≤ 2*K := by
    change ‖c • sphereSobolevDegreeL‖ ≤ _
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos hc]
    exact (mul_le_mul hcK norm_sphereSobolevDegreeL_le_two (norm_nonneg _) hK).trans_eq (by ring)
  have hN : ‖N‖ ≤ D := by
    have hEq : N = (N-A0)+A0 := by abel
    calc
      _ ≤ ‖N-A0‖+‖A0‖ := (congrArg norm hEq).le.trans (norm_add_le _ _)
      _ ≤ (CN1+CN2)*r+2*K := add_le_add hNDiff hA0
      _ ≤ (CN1+CN2)*1+2*K := by gcongr
      _ = D := by dsimp [D];ring
  have hHR' : ‖H-P0-r • P1‖ ≤ CRI*r^2 := by
    have hEq : H-P0-r • P1 = H-P0+r • ((c⁻¹)^2 • M1) := by
      dsimp only [P1]
      rw [smul_neg,sub_neg_eq_add]
    exact (congrArg norm hEq).le.trans hHR
  have hFlat : A0.comp P0 = sphereSobolevDegreeL := by
    apply ContinuousLinearMap.ext
    intro u
    change c • sphereSobolevDegreeL (c⁻¹ • u) = _
    exact (congrArg (fun z : SphereSobolev 0 => c • z) (sphereSobolevDegreeL.map_smul c⁻¹ u)).trans
      (smul_inv_smul₀ hc.ne' _)
  have hScale : c*(c⁻¹)^2 = c⁻¹ := by field_simp
  have hFirst0 : A0.comp P1+N1.comp P0 = c⁻¹ • (N1-sphereSobolevDegreeL.comp M1) := by
    apply ContinuousLinearMap.ext
    intro u
    change c • sphereSobolevDegreeL (-((c⁻¹)^2 • M1 u))+N1 (c⁻¹ • u) =
      c⁻¹ • (N1 u-sphereSobolevDegreeL (M1 u))
    simp only [map_neg,map_smul,smul_neg,smul_sub,smul_smul,hScale]
    module
  have hFirstOp := hFirst0.trans hFirst
  have hp := norm_operator_poisson_taylor_le N A0 N1 H P0 P1 r D CN1 CN2 (K^2*CM1) CRI
    hr hD hCN1 hCN2 hP1N hCRI hN hNDiff hNR hHR' hP1
  have hEq := congrArg₂ (fun L F : SphereSobolev 1 →L[ℝ] SphereSobolev 0 => N.comp H-L-r • F) hFlat hFirstOp
  have hNorm := congrArg (fun T : SphereSobolev 1 →L[ℝ] SphereSobolev 0 => ‖T‖) hEq
  have hProduct : ‖N.comp H-sphereSobolevDegreeL-r • B.adjoint.comp (sphereSobolevInclusionL 1 0 (by norm_num))‖ ≤
      (D*CRI+(CN1+CN2)*(K^2*CM1)+CN2*K)*r^2 :=
    hNorm.symm.le.trans (hp.trans (by gcongr))
  have hTH : ‖Td.comp H‖ ≤ (CT*CI)*r^2 :=
    (ContinuousLinearMap.opNorm_comp_le _ _).trans ((mul_le_mul hT hH (norm_nonneg _) (mul_nonneg hCT (sq_nonneg _))).trans_eq (by ring))
  have hDiff : (N-Td).comp H-sphereSobolevDegreeL-r • B.adjoint.comp (sphereSobolevInclusionL 1 0 (by norm_num)) =
      (N.comp H-sphereSobolevDegreeL-r • B.adjoint.comp (sphereSobolevInclusionL 1 0 (by norm_num)))-Td.comp H := by
    have hSub : (N-Td).comp H = N.comp H-Td.comp H := ContinuousLinearMap.sub_comp N Td H
    have hStart := congrArg (fun T : SphereSobolev 1 →L[ℝ] SphereSobolev 0 =>
      T-sphereSobolevDegreeL-r • B.adjoint.comp (sphereSobolevInclusionL 1 0 (by norm_num))) hSub
    exact hStart.trans (by abel)
  exact (congrArg norm hDiff).le.trans ((norm_sub_le _ _).trans
    ((add_le_add hProduct hTH).trans_eq (by dsimp [D];ring)))

end ShrinkingSpheres
