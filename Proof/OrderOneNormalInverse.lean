import Proof.OrderOneBoundaryAffine
import Proof.AffineInverseTaylor

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxSynthPendingDepth 15
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.EnergyBridge OAI.AnisotropicCalderon.DirichletFamily
open OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open OAI.AnisotropicCalderon.SphereHarmonic

structure OneBoundaryTaylorData (F F0 F1 : SmoothCoefficientMatrix 2)
    (c r CI CM1 CM2 CDI CRI CT : ℝ) : Prop where
  normal_invertible : (oneBoundaryCoefficientMulL (normalCoefficientJet F)).IsInvertible
  normal_inverse_bound : ‖(oneBoundaryCoefficientMulL (normalCoefficientJet F)).inverse‖ ≤ CI
  first_normal_bound : ‖oneBoundaryCoefficientMulL (normalCoefficientJet F1)‖ ≤ CM1
  normal_remainder_bound : ‖oneBoundaryCoefficientMulL (normalCoefficientJet F)-
    c • ContinuousLinearMap.id ℝ (SphereSobolev 1)-r • oneBoundaryCoefficientMulL (normalCoefficientJet F1)‖ ≤ CM2*r^2
  inverse_difference_bound : ‖(oneBoundaryCoefficientMulL (normalCoefficientJet F)).inverse-
    c⁻¹ • ContinuousLinearMap.id ℝ (SphereSobolev 1)‖ ≤ CDI*r
  inverse_remainder_bound : ‖(oneBoundaryCoefficientMulL (normalCoefficientJet F)).inverse-
    c⁻¹ • ContinuousLinearMap.id ℝ (SphereSobolev 1)+r • ((c⁻¹)^2 • oneBoundaryCoefficientMulL (normalCoefficientJet F1))‖ ≤ CRI*r^2
  tangent_bound : ∀ j : I,‖oneBoundaryCoefficientMulL (tangentCoefficientJet F j)‖ ≤ CT*r^2

/-- Normal inverse Taylor data at H1, from shared local C1 coefficient data.
    The scalar first coefficient removes the entire linear tangential term. -/
theorem one_boundary_taylor_data_of_local_C1
    (F F0 F1 : SmoothCoefficientMatrix 2) (c r K P Q lam Lam : ℝ)
    (hc : 0 < c) (hK : 0 ≤ K) (hci : c⁻¹ ≤ K) (hr : 0 ≤ r) (hr1 : r ≤ 1)
    (hP : 0 ≤ P) (hQ : 0 ≤ Q) (s : X → ℝ)
    (hF0 : ∀ x ∈ Metric.closedBall (0:X) 2,coefficientMatrixField 2 F0 x = 1)
    (hF1 : ∀ w : UnitSphere,coefficientMatrixField 2 F1 w.val = s w.val • (1:Mat))
    (hUE : TauCeti.PDE.UniformlyEllipticOn (ballOpens:Set X) (coefficientMatrixField 2 F) lam Lam)
    (hV1 : ∀ i j,∀ x ∈ (ballOpens:Set X),|coefficientValue 2 (F1 i j) x| ≤ P)
    (hD1 : ∀ i j,∀ x ∈ (ballOpens:Set X),‖fderiv ℝ (coefficientValue 2 (F1 i j)) x‖ ≤ P)
    (hVR : ∀ i j,∀ x ∈ (ballOpens:Set X),|coefficientValue 2 ((F-c • F0-r • F1) i j) x| ≤ Q*r^2)
    (hDR : ∀ i j,∀ x ∈ (ballOpens:Set X),‖fderiv ℝ (coefficientValue 2 ((F-c • F0-r • F1) i j)) x‖ ≤ Q*r^2)
    (hSmall : K*((73*36)*P+(73*36)*Q)*r ≤ (1/2:ℝ)) :
    OneBoundaryTaylorData F F0 F1 c r (2*K) ((73*36)*P) ((73*36)*Q)
      ((2*K)*((73*36)*P+(73*36)*Q)*K)
      ((2*K)*(K*((73*36)*Q)+K^2*((73*36)*P+(73*36)*Q)*((73*36)*P))) ((73*78)*Q) := by
  let A := oneBoundaryCoefficientMulL (normalCoefficientJet F)
  let A1 := oneBoundaryCoefficientMulL (normalCoefficientJet F1)
  let A0 := c • ContinuousLinearMap.id ℝ (SphereSobolev 1)
  let CM1 := (73*36)*P
  let CM2 := (73*36)*Q
  let D := CM1+CM2
  have hCM1 : 0 ≤ CM1 := by dsimp [CM1];positivity
  have hCM2 : 0 ≤ CM2 := by dsimp [CM2];positivity
  have hD : 0 ≤ D := add_nonneg hCM1 hCM2
  have hA : A.IsInvertible := oneBoundaryCoefficientMulL_isInvertible_of_pos (normalCoefficientJet F) (by
    intro w
    exact (congrArg (fun z : ℝ => 0 < z) (congrFun (coefficientValue_normalCoefficientJet F) w.val)).mpr
      (boundaryNormalCoefficientData_pos F lam Lam hUE w))
  have hA1 : ‖A1‖ ≤ CM1 := norm_one_first_normal_coefficient_le F1 P hP hV1 hD1
  have hAR : ‖A-A0-r • A1‖ ≤ CM2*r^2 :=
    (norm_one_normal_affine_remainder_le F F0 F1 c r (Q*r^2) (mul_nonneg hQ (sq_nonneg _)) hF0 hVR hDR).trans_eq (by ring)
  have hADiff : ‖A-A0‖ ≤ D*r :=
    (norm_normal_first_difference_le A A1 c r CM2 CM1 hr hr1 hCM2 hCM1 hAR hA1).trans_eq (by dsimp [D];ring)
  obtain ⟨hA0,hInv0⟩ := scalar_identity_inverse_data (SphereSobolev 1) c hc
  have hInv : ‖A.inverse‖ ≤ 2*K :=
    (inverse_norm_le_twice_of_half_perturbation A A0 hA hA0 K hK (hInv0.trans hci)
      ((mul_le_mul_of_nonneg_left hADiff hK).trans (by convert hSmall using 1 <;> dsimp [D,CM1,CM2] <;> ring)))
  have hIDiff : ‖A.inverse-c⁻¹ • ContinuousLinearMap.id ℝ (SphereSobolev 1)‖ ≤ ((2*K)*D*K)*r := by
    have hb := norm_inverse_sub_le A A0 hA hA0 (2*K) K (D*r) (by positivity) hK
      (mul_nonneg hD hr) hInv (hInv0.trans hci) hADiff
    have hEq := scalar_identity_inverse_eq (SphereSobolev 1) c hc.ne'
    have hn := congrArg (fun T : SphereSobolev 1 →L[ℝ] SphereSobolev 1 => ‖A.inverse-T‖) hEq
    exact hn.symm.le.trans (hb.trans_eq (by ring))
  have hIR : ‖A.inverse-c⁻¹ • ContinuousLinearMap.id ℝ (SphereSobolev 1)+r • ((c⁻¹)^2 • A1)‖ ≤
      ((2*K)*(K*CM2+K^2*D*CM1))*r^2 :=
    (norm_scalar_inverse_affine_remainder_le A A1 c r (2*K) D CM1 CM2 hc hr
      (by positivity) hD hCM1 hCM2 hA hInv hADiff hA1 hAR).trans (by gcongr)
  refine ⟨hA,hInv,hA1,hAR,hIDiff,hIR,?_⟩
  intro j
  exact (norm_one_tangent_affine_remainder_le F F0 F1 c r (Q*r^2) (mul_nonneg hQ (sq_nonneg _)) s hF0 hF1 hVR hDR j).trans_eq (by ring)

end ShrinkingSpheres
