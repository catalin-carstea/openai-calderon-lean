import Proof.OrderOneCoefficientAlgebra
import Proof.BoundaryAffineRemainder

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option maxSynthPendingDepth 15
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.EnergyBridge OAI.AnisotropicCalderon.DirichletFamily
open OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open OAI.AnisotropicCalderon.SphereHarmonic

lemma oneNormalCoefficient_sub_smul (F G : SmoothCoefficientMatrix 2) (c : ℝ) :
    oneBoundaryCoefficientMulL (normalCoefficientJet (F-c • G)) =
      oneBoundaryCoefficientMulL (normalCoefficientJet F)-c • oneBoundaryCoefficientMulL (normalCoefficientJet G) := by
  have hEq := oneBoundaryCoefficientMulL_congr_sphere (normalCoefficientJet (F-c • G))
    (normalCoefficientJet F-c • normalCoefficientJet G) (by
      intro w
      rw [coefficientValue_normalCoefficientJet,coefficientValue_sub_local,coefficientValue_smul]
      change (boundaryNormalCoefficientData (F-c • G)).1 w.val =
        coefficientValue 2 (normalCoefficientJet F) w.val-c*coefficientValue 2 (normalCoefficientJet G) w.val
      rw [coefficientValue_normalCoefficientJet,coefficientValue_normalCoefficientJet,boundaryNormalCoefficient_sub_smul])
  exact hEq.trans ((oneBoundaryCoefficientMulL_sub _ _).trans
    (congrArg (fun T => oneBoundaryCoefficientMulL (normalCoefficientJet F)-T) (oneBoundaryCoefficientMulL_smul c _)))

lemma oneTangentCoefficient_sub_smul (F G : SmoothCoefficientMatrix 2) (c : ℝ) (j : I) :
    oneBoundaryCoefficientMulL (tangentCoefficientJet (F-c • G) j) =
      oneBoundaryCoefficientMulL (tangentCoefficientJet F j)-c • oneBoundaryCoefficientMulL (tangentCoefficientJet G j) := by
  have hEq := oneBoundaryCoefficientMulL_congr_sphere (tangentCoefficientJet (F-c • G) j)
    (tangentCoefficientJet F j-c • tangentCoefficientJet G j) (by
      intro w
      rw [coefficientValue_tangentCoefficientJet,coefficientValue_sub_local,coefficientValue_smul]
      change (boundaryTangentCoefficientData (F-c • G) j).1 w.val =
        coefficientValue 2 (tangentCoefficientJet F j) w.val-c*coefficientValue 2 (tangentCoefficientJet G j) w.val
      rw [coefficientValue_tangentCoefficientJet,coefficientValue_tangentCoefficientJet,boundaryTangentCoefficient_sub_smul])
  exact hEq.trans ((oneBoundaryCoefficientMulL_sub _ _).trans
    (congrArg (fun T => oneBoundaryCoefficientMulL (tangentCoefficientJet F j)-T) (oneBoundaryCoefficientMulL_smul c _)))

lemma oneNormalCoefficient_flat (F0 : SmoothCoefficientMatrix 2)
    (hF0 : ∀ x ∈ Metric.closedBall (0:X) 2,coefficientMatrixField 2 F0 x = 1) :
    oneBoundaryCoefficientMulL (normalCoefficientJet F0) = ContinuousLinearMap.id ℝ (SphereSobolev 1) := by
  have h := oneBoundaryCoefficientMulL_const_sphere (normalCoefficientJet F0) 1 (by
    intro w
    exact (congrFun (coefficientValue_normalCoefficientJet F0) w.val).trans (boundaryNormalCoefficient_flat_sphere F0 hF0 w))
  exact h.trans (one_smul _ _)

lemma oneTangentCoefficient_scalar_zero (F : SmoothCoefficientMatrix 2) (q : X → ℝ)
    (hF : ∀ w : UnitSphere,coefficientMatrixField 2 F w.val = q w.val • (1:Mat)) (j : I) :
    oneBoundaryCoefficientMulL (tangentCoefficientJet F j) = 0 := by
  have h := oneBoundaryCoefficientMulL_const_sphere (tangentCoefficientJet F j) 0 (by
    intro w
    rw [coefficientValue_tangentCoefficientJet]
    change (∑ i : I,w.val i*coefficientValue 2 (F i j) w.val)-
      (boundaryNormalCoefficientData F).1 w.val*w.val j = 0
    rw [boundaryNormalCoefficient_scalar_sphere F q hF w]
    have hEntry (i : I) : coefficientValue 2 (F i j) w.val = q w.val*(1:Mat) i j :=
      congrArg (fun A : Mat => A i j) (hF w)
    simp_rw [hEntry]
    simp [Matrix.one_apply]
    ring)
  exact h.trans (zero_smul _ _)

theorem norm_one_normal_affine_remainder_le (F F0 F1 : SmoothCoefficientMatrix 2)
    (c r q : ℝ) (hq : 0 ≤ q)
    (hF0 : ∀ x ∈ Metric.closedBall (0:X) 2,coefficientMatrixField 2 F0 x = 1)
    (hValue : ∀ i j,∀ x ∈ (ballOpens:Set X),|coefficientValue 2 ((F-c • F0-r • F1) i j) x| ≤ q)
    (hDerivative : ∀ i j,∀ x ∈ (ballOpens:Set X),‖fderiv ℝ (coefficientValue 2 ((F-c • F0-r • F1) i j)) x‖ ≤ q) :
    ‖oneBoundaryCoefficientMulL (normalCoefficientJet F)-c • ContinuousLinearMap.id ℝ (SphereSobolev 1)-
      r • oneBoundaryCoefficientMulL (normalCoefficientJet F1)‖ ≤ (73*36)*q := by
  have hC1 := normalCoefficientJet_local_C1 (F-c • F0-r • F1) q hq hValue hDerivative
  have hb := norm_oneBoundaryCoefficientMulL_local_C1 (normalCoefficientJet (F-c • F0-r • F1)) (36*q) (by positivity) hC1
  have hEq : oneBoundaryCoefficientMulL (normalCoefficientJet (F-c • F0-r • F1)) =
      oneBoundaryCoefficientMulL (normalCoefficientJet F)-c • ContinuousLinearMap.id ℝ (SphereSobolev 1)-
        r • oneBoundaryCoefficientMulL (normalCoefficientJet F1) := by
    rw [oneNormalCoefficient_sub_smul,oneNormalCoefficient_sub_smul,oneNormalCoefficient_flat F0 hF0]
  exact (congrArg norm hEq).symm.le.trans (hb.trans_eq (by ring))

theorem norm_one_tangent_affine_remainder_le (F F0 F1 : SmoothCoefficientMatrix 2)
    (c r q : ℝ) (hq : 0 ≤ q) (s : X → ℝ)
    (hF0 : ∀ x ∈ Metric.closedBall (0:X) 2,coefficientMatrixField 2 F0 x = 1)
    (hF1 : ∀ w : UnitSphere,coefficientMatrixField 2 F1 w.val = s w.val • (1:Mat))
    (hValue : ∀ i j,∀ x ∈ (ballOpens:Set X),|coefficientValue 2 ((F-c • F0-r • F1) i j) x| ≤ q)
    (hDerivative : ∀ i j,∀ x ∈ (ballOpens:Set X),‖fderiv ℝ (coefficientValue 2 ((F-c • F0-r • F1) i j)) x‖ ≤ q)
    (j : I) : ‖oneBoundaryCoefficientMulL (tangentCoefficientJet F j)‖ ≤ (73*78)*q := by
  have hC1 := tangentCoefficientJet_local_C1 (F-c • F0-r • F1) q hq hValue hDerivative j
  have hb := norm_oneBoundaryCoefficientMulL_local_C1 (tangentCoefficientJet (F-c • F0-r • F1) j) (78*q) (by positivity) hC1
  have hFlat : oneBoundaryCoefficientMulL (tangentCoefficientJet F0 j) = 0 :=
    oneTangentCoefficient_scalar_zero F0 (fun _ => 1) (by
      intro w
      have hw := Metric.closedBall_subset_closedBall (by norm_num : (1:ℝ) ≤ 2) (Metric.sphere_subset_closedBall w.property)
      simpa only [one_smul] using hF0 w.val hw) j
  have hEq : oneBoundaryCoefficientMulL (tangentCoefficientJet (F-c • F0-r • F1) j) =
      oneBoundaryCoefficientMulL (tangentCoefficientJet F j) := by
    rw [oneTangentCoefficient_sub_smul,oneTangentCoefficient_sub_smul,
      oneTangentCoefficient_scalar_zero F1 s hF1 j,hFlat,smul_zero,smul_zero,sub_zero,sub_zero]
  exact (congrArg norm hEq).symm.le.trans (hb.trans_eq (by ring))

theorem norm_one_first_normal_coefficient_le (F1 : SmoothCoefficientMatrix 2) (P : ℝ) (hP : 0 ≤ P)
    (hValue : ∀ i j,∀ x ∈ (ballOpens:Set X),|coefficientValue 2 (F1 i j) x| ≤ P)
    (hDerivative : ∀ i j,∀ x ∈ (ballOpens:Set X),‖fderiv ℝ (coefficientValue 2 (F1 i j)) x‖ ≤ P) :
    ‖oneBoundaryCoefficientMulL (normalCoefficientJet F1)‖ ≤ (73*36)*P :=
  (norm_oneBoundaryCoefficientMulL_local_C1 (normalCoefficientJet F1) (36*P) (by positivity)
    (normalCoefficientJet_local_C1 F1 P hP hValue hDerivative)).trans_eq (by ring)

end ShrinkingSpheres
