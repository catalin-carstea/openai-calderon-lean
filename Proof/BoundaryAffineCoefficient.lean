import Proof.NegativeNormalInverse
import Proof.PullbackCoefficientRepresentative

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

lemma negativeBoundaryCoefficientMulL_zero : negativeBoundaryCoefficientMulL (0:SmoothCoefficientJets 2) = 0 := by
  have h := negativeBoundaryCoefficientMulL_smul 0 (0:SmoothCoefficientJets 2)
  simpa only [zero_smul] using h

lemma negativeBoundaryCoefficientMulL_sub (F G : SmoothCoefficientJets 2) :
    negativeBoundaryCoefficientMulL (F-G) = negativeBoundaryCoefficientMulL F-negativeBoundaryCoefficientMulL G := by
  rw [sub_eq_add_neg,← neg_one_smul ℝ G,negativeBoundaryCoefficientMulL_add,negativeBoundaryCoefficientMulL_smul]
  module

lemma negativeNormalCoefficient_sub_smul (F G : SmoothCoefficientMatrix 2) (c : ℝ) :
    negativeBoundaryCoefficientMulL (normalCoefficientJet (F-c • G)) =
      negativeBoundaryCoefficientMulL (normalCoefficientJet F)-c • negativeBoundaryCoefficientMulL (normalCoefficientJet G) := by
  have hEq := negativeBoundaryCoefficientMulL_congr_sphere (normalCoefficientJet (F-c • G))
    (normalCoefficientJet F-c • normalCoefficientJet G) (by
      intro w
      rw [coefficientValue_normalCoefficientJet,coefficientValue_sub_local,coefficientValue_smul]
      change (boundaryNormalCoefficientData (F-c • G)).1 w.val =
        coefficientValue 2 (normalCoefficientJet F) w.val-c*coefficientValue 2 (normalCoefficientJet G) w.val
      rw [coefficientValue_normalCoefficientJet,coefficientValue_normalCoefficientJet,boundaryNormalCoefficient_sub_smul])
  rw [hEq,negativeBoundaryCoefficientMulL_sub,negativeBoundaryCoefficientMulL_smul]

lemma negativeTangentCoefficient_sub_smul (F G : SmoothCoefficientMatrix 2) (c : ℝ) (j : I) :
    negativeBoundaryCoefficientMulL (tangentCoefficientJet (F-c • G) j) =
      negativeBoundaryCoefficientMulL (tangentCoefficientJet F j)-c • negativeBoundaryCoefficientMulL (tangentCoefficientJet G j) := by
  have hEq := negativeBoundaryCoefficientMulL_congr_sphere (tangentCoefficientJet (F-c • G) j)
    (tangentCoefficientJet F j-c • tangentCoefficientJet G j) (by
      intro w
      rw [coefficientValue_tangentCoefficientJet,coefficientValue_sub_local,coefficientValue_smul]
      change (boundaryTangentCoefficientData (F-c • G) j).1 w.val =
        coefficientValue 2 (tangentCoefficientJet F j) w.val-c*coefficientValue 2 (tangentCoefficientJet G j) w.val
      rw [coefficientValue_tangentCoefficientJet,coefficientValue_tangentCoefficientJet,boundaryTangentCoefficient_sub_smul])
  rw [hEq,negativeBoundaryCoefficientMulL_sub,negativeBoundaryCoefficientMulL_smul]

lemma boundaryNormalCoefficient_scalar_sphere (F : SmoothCoefficientMatrix 2) (q : X → ℝ)
    (hF : ∀ w : UnitSphere,coefficientMatrixField 2 F w.val = q w.val • (1:Mat)) (w : UnitSphere) :
    (boundaryNormalCoefficientData F).1 w.val = q w.val := by
  have hEntry (i j : I) : coefficientValue 2 (F i j) w.val = q w.val*(1:Mat) i j :=
    congrArg (fun A : Mat => A i j) (hF w)
  change (∑ i : I,∑ j : I,w.val i*coefficientValue 2 (F i j) w.val*w.val j) = q w.val
  simp_rw [hEntry]
  calc
    _ = q w.val*∑ i : I,(w.val i)^2 := by
      simp only [Fin.sum_univ_three,Matrix.one_apply]
      norm_num
      ring
    _ = _ := by rw [unitSphere_sum_sq,mul_one]

lemma negativeTangentCoefficient_scalar_zero (F : SmoothCoefficientMatrix 2) (q : X → ℝ)
    (hF : ∀ w : UnitSphere,coefficientMatrixField 2 F w.val = q w.val • (1:Mat)) (j : I) :
    negativeBoundaryCoefficientMulL (tangentCoefficientJet F j) = 0 := by
  rw [← negativeBoundaryCoefficientMulL_zero]
  apply negativeBoundaryCoefficientMulL_congr_sphere
  intro w
  rw [coefficientValue_tangentCoefficientJet]
  change (∑ i : I,w.val i*coefficientValue 2 (F i j) w.val)-
    (boundaryNormalCoefficientData F).1 w.val*w.val j = 0
  rw [boundaryNormalCoefficient_scalar_sphere F q hF w]
  have hEntry (i : I) : coefficientValue 2 (F i j) w.val = q w.val*(1:Mat) i j :=
    congrArg (fun A : Mat => A i j) (hF w)
  simp_rw [hEntry]
  simp [Matrix.one_apply]
  ring

/-- The actual normal multiplier has the affine model's normal first
    variation, with a quadratic perturbation controlled in local C1. -/
theorem norm_negative_normal_affine_remainder_le (F F0 F1 : SmoothCoefficientMatrix 2)
    (c r q : ℝ) (hq : 0 ≤ q)
    (hF0 : ∀ x ∈ Metric.closedBall (0:X) 2,coefficientMatrixField 2 F0 x = 1)
    (hValue : ∀ i j,∀ x ∈ (ballOpens:Set X),|coefficientValue 2 ((F-c • F0-r • F1) i j) x| ≤ q)
    (hDerivative : ∀ i j,∀ x ∈ (ballOpens:Set X),‖fderiv ℝ (coefficientValue 2 ((F-c • F0-r • F1) i j)) x‖ ≤ q) :
    ‖negativeBoundaryCoefficientMulL (normalCoefficientJet F)-
      c • ContinuousLinearMap.id ℝ (SphereSobolev (-(1/2:ℝ)))-
      r • negativeBoundaryCoefficientMulL (normalCoefficientJet F1)‖ ≤ boundaryHalfMultiplierBudget*(36*q) := by
  have hC1 := normalCoefficientJet_local_C1 (F-c • F0-r • F1) q hq hValue hDerivative
  have hb := norm_nativeNegativeHalfCoefficientMulL_local_C1 (normalCoefficientJet (F-c • F0-r • F1))
    (36*q) (by positivity) (fun x hx => (hC1 x hx).1) (fun x hx => (hC1 x hx).2)
  have hEq : negativeBoundaryCoefficientMulL (normalCoefficientJet F)-
      c • ContinuousLinearMap.id ℝ (SphereSobolev (-(1/2:ℝ)))-
      r • negativeBoundaryCoefficientMulL (normalCoefficientJet F1) =
      negativeBoundaryCoefficientMulL (normalCoefficientJet (F-c • F0-r • F1)) := by
    rw [negativeNormalCoefficient_sub_smul]
    have h0 := negative_normal_coefficient_decomposition F F0 c hF0
    rw [h0]
    abel
  rw [hEq]
  exact hb

end ShrinkingSpheres
