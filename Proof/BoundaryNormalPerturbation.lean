import Proof.BoundaryCoefficientRepresentatives

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxSynthPendingDepth 15
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set
open scoped ContDiff ENNReal
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.EnergyBridge OAI.AnisotropicCalderon.DirichletFamily
open OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open OAI.AnisotropicCalderon.SphereHarmonic OAI.AnisotropicCalderon.SpectralCoreRegularity

lemma boundaryNormalCoefficient_sub_smul (F G : SmoothCoefficientMatrix 2) (c : ℝ) (x : X) :
    (boundaryNormalCoefficientData (F-c • G)).1 x =
      (boundaryNormalCoefficientData F).1 x-c*(boundaryNormalCoefficientData G).1 x := by
  have hEntry (i j : I) : coefficientValue 2 ((F-c • G) i j) x =
      coefficientValue 2 (F i j) x-c*coefficientValue 2 (G i j) x := by rfl
  change (∑ i : I,∑ j : I,x i*coefficientValue 2 ((F-c • G) i j) x*x j) =
    (∑ i : I,∑ j : I,x i*coefficientValue 2 (F i j) x*x j)-
      c*(∑ i : I,∑ j : I,x i*coefficientValue 2 (G i j) x*x j)
  simp_rw [hEntry]
  simp only [Fin.sum_univ_three]
  ring

lemma boundaryTangentCoefficient_sub_smul (F G : SmoothCoefficientMatrix 2) (c : ℝ) (j : I) (x : X) :
    (boundaryTangentCoefficientData (F-c • G) j).1 x =
      (boundaryTangentCoefficientData F j).1 x-c*(boundaryTangentCoefficientData G j).1 x := by
  have hEntry (i : I) : coefficientValue 2 ((F-c • G) i j) x =
      coefficientValue 2 (F i j) x-c*coefficientValue 2 (G i j) x := by rfl
  change (∑ i : I,x i*coefficientValue 2 ((F-c • G) i j) x)-
      (boundaryNormalCoefficientData (F-c • G)).1 x*x j =
    ((∑ i : I,x i*coefficientValue 2 (F i j) x)-(boundaryNormalCoefficientData F).1 x*x j)-
      c*((∑ i : I,x i*coefficientValue 2 (G i j) x)-(boundaryNormalCoefficientData G).1 x*x j)
  rw [boundaryNormalCoefficient_sub_smul]
  simp_rw [hEntry]
  simp only [Fin.sum_univ_three]
  ring

lemma boundaryNormalCoefficient_flat_sphere (F0 : SmoothCoefficientMatrix 2)
    (hF0 : ∀ x ∈ Metric.closedBall (0:X) 2,coefficientMatrixField 2 F0 x = 1)
    (w : UnitSphere) : (boundaryNormalCoefficientData F0).1 w.val = 1 := by
  have hOne : w.val ∈ Metric.closedBall (0:X) 1 := Metric.sphere_subset_closedBall w.property
  have hTwo : w.val ∈ Metric.closedBall (0:X) 2 := Metric.closedBall_subset_closedBall (by norm_num) hOne
  have hEntry (i j : I) : coefficientValue 2 (F0 i j) w.val = (1:Mat) i j :=
    congrArg (fun A : Mat => A i j) (hF0 w.val hTwo)
  change (∑ i : I,∑ j : I,w.val i*coefficientValue 2 (F0 i j) w.val*w.val j) = 1
  simp_rw [hEntry]
  calc
    _ = ∑ i : I,(w.val i)^2 := by simp [Matrix.one_apply,pow_two]
    _ = 1 := unitSphere_sum_sq w

lemma boundaryTangentCoefficient_flat_sphere (F0 : SmoothCoefficientMatrix 2)
    (hF0 : ∀ x ∈ Metric.closedBall (0:X) 2,coefficientMatrixField 2 F0 x = 1)
    (j : I) (w : UnitSphere) : (boundaryTangentCoefficientData F0 j).1 w.val = 0 := by
  have hOne : w.val ∈ Metric.closedBall (0:X) 1 := Metric.sphere_subset_closedBall w.property
  have hTwo : w.val ∈ Metric.closedBall (0:X) 2 := Metric.closedBall_subset_closedBall (by norm_num) hOne
  have hEntry (i : I) : coefficientValue 2 (F0 i j) w.val = (1:Mat) i j :=
    congrArg (fun A : Mat => A i j) (hF0 w.val hTwo)
  change (∑ i : I,w.val i*coefficientValue 2 (F0 i j) w.val)-
    (boundaryNormalCoefficientData F0).1 w.val*w.val j = 0
  rw [boundaryNormalCoefficient_flat_sphere F0 hF0 w]
  simp_rw [hEntry]
  simp [Matrix.one_apply]

/-- The actual normal coefficient operator is its scalar flat center plus the
    operator of the small perturbation's normal coefficient. -/
theorem negative_normal_coefficient_decomposition (F F0 : SmoothCoefficientMatrix 2) (c : ℝ)
    (hF0 : ∀ x ∈ Metric.closedBall (0:X) 2,coefficientMatrixField 2 F0 x = 1) :
    negativeBoundaryCoefficientMulL (normalCoefficientJet F) =
      c • ContinuousLinearMap.id ℝ (SphereSobolev (-(1/2:ℝ)))+
        negativeBoundaryCoefficientMulL (normalCoefficientJet (F-c • F0)) := by
  let B := F0 (0:I) (0:I)
  let D := normalCoefficientJet (F-c • F0)
  have hB (x : X) (hx : x ∈ (ballOpens : Set X)) : coefficientValue 2 B x = 1 := by
    have hOne : x ∈ Metric.closedBall (0:X) 1 := Metric.ball_subset_closedBall hx
    have hTwo : x ∈ Metric.closedBall (0:X) 2 := Metric.closedBall_subset_closedBall (by norm_num) hOne
    change coefficientMatrixField 2 F0 x (0:I) (0:I) = 1
    simpa only [Matrix.one_apply,ite_true] using congrArg (fun A : Mat => A (0:I) (0:I)) (hF0 x hTwo)
  have hSphere (w : UnitSphere) : coefficientValue 2 (normalCoefficientJet F) w.val =
      coefficientValue 2 (c • B+D) w.val := by
    have hOne : w.val ∈ Metric.closedBall (0:X) 1 := Metric.sphere_subset_closedBall w.property
    have hTwo : w.val ∈ Metric.closedBall (0:X) 2 := Metric.closedBall_subset_closedBall (by norm_num) hOne
    have hBw : coefficientValue 2 B w.val = 1 := by
      change coefficientMatrixField 2 F0 w.val (0:I) (0:I) = 1
      simpa only [Matrix.one_apply,ite_true] using congrArg (fun A : Mat => A (0:I) (0:I)) (hF0 w.val hTwo)
    rw [coefficientValue_add,coefficientValue_smul,coefficientValue_normalCoefficientJet F]
    change (boundaryNormalCoefficientData F).1 w.val = c*coefficientValue 2 B w.val+
      (boundaryNormalCoefficientData (F-c • F0)).1 w.val
    rw [hBw,boundaryNormalCoefficient_sub_smul,boundaryNormalCoefficient_flat_sphere F0 hF0 w]
    ring
  calc
    _ = negativeBoundaryCoefficientMulL (c • B+D) :=
      negativeBoundaryCoefficientMulL_congr_sphere _ _ hSphere
    _ = negativeBoundaryCoefficientMulL (c • B)+negativeBoundaryCoefficientMulL D :=
      negativeBoundaryCoefficientMulL_add _ _
    _ = c • negativeBoundaryCoefficientMulL B+negativeBoundaryCoefficientMulL D :=
      congrArg (fun T => T+negativeBoundaryCoefficientMulL D) (negativeBoundaryCoefficientMulL_smul c B)
    _ = _ := congrArg (fun T => c • T+negativeBoundaryCoefficientMulL D) (negativeBoundaryCoefficientMulL_one B hB)

/-- Flat scalar coefficients have no tangential boundary contribution. -/
theorem negative_tangent_coefficient_decomposition (F F0 : SmoothCoefficientMatrix 2) (c : ℝ)
    (hF0 : ∀ x ∈ Metric.closedBall (0:X) 2,coefficientMatrixField 2 F0 x = 1) (j : I) :
    negativeBoundaryCoefficientMulL (tangentCoefficientJet F j) =
      negativeBoundaryCoefficientMulL (tangentCoefficientJet (F-c • F0) j) := by
  apply negativeBoundaryCoefficientMulL_congr_sphere
  intro w
  rw [coefficientValue_tangentCoefficientJet,coefficientValue_tangentCoefficientJet,
    boundaryTangentCoefficient_sub_smul,boundaryTangentCoefficient_flat_sphere F0 hF0 j w]
  simp

end ShrinkingSpheres
