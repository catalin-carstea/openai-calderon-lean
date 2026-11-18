import Proof.ClosedCoordinateCoefficientProduct
import Proof.CoordinateScalarRotationPacket
import Proof.DenseOperatorRestrictionUnique
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2600000
set_option maxSynthPendingDepth 30
set_option maxRecDepth 2200
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter
open scoped ContDiff Topology InnerProductSpace
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.DirichletFamily OAI.AnisotropicCalderon.SphereHarmonic

lemma closedOneBoundaryScalarMultiplier_fixed_product (P : SmoothCoefficientJets 3)
    (Q : ClosedCoefficientJets 3) :
    closedOneBoundaryScalarMultiplierL (closedCoefficientFixedProductL 3 P Q)=
      (closedOneBoundaryScalarMultiplierL (smoothCoefficientClosureInclusionL 3 P)).comp
        (closedOneBoundaryScalarMultiplierL Q) := by
  apply ContinuousLinearMap.ext
  intro u
  apply sphereSobolevInclusionL_injective 1 0 (by norm_num)
  simp only [ContinuousLinearMap.comp_apply,closedThreeJet_scalar_multiplier_compatible]
  exact DFunLike.congr_fun (closedThreeJetCoarseScalarMultiplier_fixed_product P Q)
    (sphereSobolevInclusionL 1 0 (by norm_num) u)

lemma closedCoefficientAngularCoarse_fixed_product (P : SmoothCoefficientJets 3)
    (Q : ClosedCoefficientJets 3) (i j : I) :
    closedCoefficientAngularCoarseL i j (closedCoefficientFixedProductL 3 P Q)=
      (closedCoefficientAngularCoarseL i j (smoothCoefficientClosureInclusionL 3 P)).comp
        (closedThreeJetCoarseScalarMultiplierL Q)+
      (closedThreeJetCoarseScalarMultiplierL (smoothCoefficientClosureInclusionL 3 P)).comp
        (closedCoefficientAngularCoarseL i j Q) := by
  apply clm_eq_of_dense_restriction (sphereSobolevInclusionL 1 0 (by norm_num))
    (denseRange_sphereSobolevInclusionL 1 0 (by norm_num))
  apply ContinuousLinearMap.ext
  intro u
  let P0 := smoothCoefficientClosureInclusionL 3 P
  have hProd := closedCoefficientMultiplier_rotation_product i j (closedCoefficientFixedProductL 3 P Q) u
  have hP := closedCoefficientMultiplier_rotation_product i j P0 (closedOneBoundaryScalarMultiplierL Q u)
  have hQ := closedCoefficientMultiplier_rotation_product i j Q u
  rw [closedOneBoundaryScalarMultiplier_fixed_product,ContinuousLinearMap.comp_apply,
    closedThreeJetCoarseScalarMultiplier_fixed_product,ContinuousLinearMap.comp_apply] at hProd
  change sphereSobolevRotationL 1 i j (closedOneBoundaryScalarMultiplierL P0
    (closedOneBoundaryScalarMultiplierL Q u))=_ at hProd
  have hFirst := congrArg (closedCoefficientAngularCoarseL i j P0)
    (closedThreeJet_scalar_multiplier_compatible Q u)
  have hSecond := (congrArg (closedThreeJetCoarseScalarMultiplierL P0) hQ).trans
    (ContinuousLinearMap.map_add _ _ _)
  have hExpanded := hP.trans (congrArg₂ (fun v w : SphereSobolev 0 => v+w) hFirst hSecond)
  exact add_right_cancel (hProd.symm.trans (hExpanded.trans (add_assoc _ _ _).symm))

lemma closedCoefficientAngularHalf_fixed_product (P : SmoothCoefficientJets 3)
    (Q : ClosedCoefficientJets 3) (i j : I) :
    closedCoefficientAngularHalfL i j (closedCoefficientFixedProductL 3 P Q)=
      (closedCoefficientAngularHalfL i j (smoothCoefficientClosureInclusionL 3 P)).comp
        (closedThreeJetHalfBoundaryScalarMultiplierL Q)+
      (closedThreeJetHalfBoundaryScalarMultiplierL (smoothCoefficientClosureInclusionL 3 P)).comp
        (closedCoefficientAngularHalfL i j Q) := by
  apply ContinuousLinearMap.ext
  intro u
  apply sphereSobolevInclusionL_injective (1/2:ℝ) 0 (by norm_num)
  simp only [_root_.add_apply,ContinuousLinearMap.comp_apply,ContinuousLinearMap.map_add,
    closedCoefficientAngularHalfL_coarse,closedThreeJet_half_scalar_multiplier_coarse]
  exact DFunLike.congr_fun (closedCoefficientAngularCoarse_fixed_product P Q i j)
    (sphereSobolevInclusionL (1/2:ℝ) 0 (by norm_num) u)

lemma closedCoefficientAngularCoarse_eq_of_rotation_data (Q : ClosedCoefficientJets 3)
    (D : ScalarRotationMultiplierData)
    (hOne : closedOneBoundaryScalarMultiplierL Q=D.one)
    (hCoarse : closedThreeJetCoarseScalarMultiplierL Q=D.coarse) (i j : I) :
    closedCoefficientAngularCoarseL i j Q=D.angularCoarse (i,j) := by
  apply clm_eq_of_dense_restriction (sphereSobolevInclusionL 1 0 (by norm_num))
    (denseRange_sphereSobolevInclusionL 1 0 (by norm_num))
  apply ContinuousLinearMap.ext
  intro u
  have hQ := closedCoefficientMultiplier_rotation_product i j Q u
  rw [hOne,hCoarse] at hQ
  exact add_right_cancel (hQ.symm.trans (D.product (i,j) u))

lemma coordinateScalarClosedJet_angular_coarse (Q0 : SmoothCoefficientJets 2)
    (hQ0 : ∀ z ∈ Metric.closedBall (0:X) 1,coefficientValue 2 Q0 =ᶠ[𝓝 z] (fun _ => (1:ℝ)))
    (k i j : I) :
    closedCoefficientAngularCoarseL i j (smoothCoefficientClosureInclusionL 3 (coordinateScalarSmoothJet Q0 k))=
      coordinateAngularCoarseMul i j k := by
  exact closedCoefficientAngularCoarse_eq_of_rotation_data _ (coordinateScalarRotationData k)
    (by
      apply ContinuousLinearMap.ext
      intro u
      apply sphereSobolevInclusionL_injective 1 0 (by norm_num)
      change _=sphereSobolevInclusionL 1 0 (by norm_num) (oneSphereCoordinateMulL k u)
      rw [closedThreeJet_scalar_multiplier_compatible,coordinateScalarClosedJet_coarse Q0 hQ0,
        coordinateMultiplierSobolevL_zero]
      exact (oneSphereCoordinateMulL_coarse k u).symm)
    (by
      rw [coordinateScalarClosedJet_coarse Q0 hQ0,coordinateMultiplierSobolevL_zero]
      rfl) i j

lemma coordinateScalarClosedJet_angular_half (Q0 : SmoothCoefficientJets 2)
    (hQ0 : ∀ z ∈ Metric.closedBall (0:X) 1,coefficientValue 2 Q0 =ᶠ[𝓝 z] (fun _ => (1:ℝ)))
    (k i j : I) :
    closedCoefficientAngularHalfL i j (smoothCoefficientClosureInclusionL 3 (coordinateScalarSmoothJet Q0 k))=
      (if k=j then coordinateMultiplierSobolevL (1/2:ℝ) i else 0)-
        (if k=i then coordinateMultiplierSobolevL (1/2:ℝ) j else 0) := by
  apply ContinuousLinearMap.ext
  intro u
  apply sphereSobolevInclusionL_injective (1/2:ℝ) 0 (by norm_num)
  rw [closedCoefficientAngularHalfL_coarse,coordinateScalarClosedJet_angular_coarse Q0 hQ0]
  unfold coordinateAngularCoarseMul
  split_ifs <;> simp only [_root_.sub_apply,_root_.zero_apply,ContinuousLinearMap.map_sub,
    ContinuousLinearMap.map_zero,coordinateMultiplierSobolevL_half_coarse]

lemma closedUnitCoefficient_angular_half (Q0 : SmoothCoefficientJets 2)
    (hQ0 : ∀ z ∈ Metric.closedBall (0:X) 1,coefficientValue 2 Q0 =ᶠ[𝓝 z] (fun _ => (1:ℝ)))
    (i j : I) : closedCoefficientAngularHalfL i j (closedUnitCoefficient Q0)=0 := by
  have hC : closedCoefficientAngularCoarseL i j (closedUnitCoefficient Q0)=0 := by
    apply clm_eq_of_dense_restriction (sphereSobolevInclusionL 1 0 (by norm_num))
      (denseRange_sphereSobolevInclusionL 1 0 (by norm_num))
    apply ContinuousLinearMap.ext
    intro u
    have hh := closedCoefficientMultiplier_rotation_product i j (closedUnitCoefficient Q0) u
    rw [closedUnitCoefficient_one Q0 hQ0,closedUnitCoefficient_coarse Q0 hQ0] at hh
    change sphereSobolevRotationL 1 i j u=_ at hh
    exact add_right_cancel (hh.symm.trans (zero_add _).symm)
  apply ContinuousLinearMap.ext
  intro u
  apply sphereSobolevInclusionL_injective (1/2:ℝ) 0 (by norm_num)
  rw [closedCoefficientAngularHalfL_coarse,hC]
  exact (sphereSobolevInclusionL (1/2:ℝ) 0 (by norm_num)).map_zero.symm
end ShrinkingSpheres
