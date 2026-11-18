import Proof.NormalFrameCoefficientModel
import Proof.OrthogonalMatrixCoefficientCovariance
import Proof.CoordinateRotationGenerator

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped ContDiff Topology Matrix.Norms.Elementwise
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.EnergyBridge OAI.AnisotropicCalderon.DirichletFamily
open OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open OAI.AnisotropicCalderon.MetricOperator OAI.AnisotropicCalderon.SmoothSphereRotation
open OAI.AnisotropicCalderon.ConnectionError

/-- Rotating the frame conjugates the true normal metric, with the same
    rotation of its spatial argument. This uses the actual bilinear pullback
    tensor and holds without geometric or regularity hypotheses. -/
theorem normalFrameMetric_coordinate_rotation (g : MetricField) (E : X × X → X)
    (y : X) (s : ℝ) (L : X →L[ℝ] X) (i j : I) (θ : ℝ) (z : X) :
    normalFrameMetric g E ((y,(s,L.comp (coordinateRotationIsometry i j θ).toContinuousLinearEquiv.toContinuousLinearMap)),z) =
      (coordinateRotationMatrix i j θ).transpose*
        normalFrameMetric g E ((y,(s,L)),coordinateRotation i j θ z)*coordinateRotationMatrix i j θ := by
  let R : X →L[ℝ] X := (coordinateRotationIsometry i j θ).toContinuousLinearEquiv.toContinuousLinearMap
  let Q := coordinateRotationMatrix i j θ
  have hEntry (k l : I) : Q k l = R (axis l) k := coordinateRotationMatrix_entry i j k l θ
  have hSlot (k : I) : R (axis k) = ∑ l,Q l k • axis l := by
    simpa only [hEntry] using (axis_expansion (R (axis k))).symm
  let T := normalJointMetricTensor g E (y,s • L (R z))
  ext k l
  change jointNormalMetricPair g E (L (R (axis k))) (L (R (axis l))) (y,s • L (R z)) =
    (Q.transpose*normalFrameMetric g E ((y,(s,L)),R z)*Q) k l
  rw [← normalJointMetricTensor_apply]
  change T (L (R (axis k))) (L (R (axis l))) =
    (Q.transpose*normalFrameMetric g E ((y,(s,L)),R z)*Q) k l
  rw [hSlot k,hSlot l]
  simp only [map_sum,map_smul,_root_.sum_apply,_root_.smul_apply,Finset.smul_sum,smul_smul,smul_eq_mul]
  simp only [Matrix.mul_apply,Matrix.transpose_apply,normalFrameMetric,normalFrameInput,
    T,normalJointMetricTensor_apply,Fin.sum_univ_three]
  ring

lemma coordinateRotationMatrix_orthogonal (i j : I) (θ : ℝ) :
    (coordinateRotationMatrix i j θ).transpose*coordinateRotationMatrix i j θ = 1 ∧
      coordinateRotationMatrix i j θ*(coordinateRotationMatrix i j θ).transpose = 1 := by
  let e := coordinateRotationIsometry i j θ
  let R := e.toContinuousLinearEquiv.toContinuousLinearMap
  let Ri := e.symm.toContinuousLinearEquiv.toContinuousLinearMap
  have hTranspose : operatorMatrixMap Ri = (operatorMatrixMap R).transpose := by
    rw [show Ri = R.adjoint by exact e.adjoint_eq_symm.symm]
    exact operatorMatrixMap_adjoint _
  have hLeft : Ri.comp R = ContinuousLinearMap.id ℝ X := by
    apply ContinuousLinearMap.ext
    intro z
    exact e.symm_apply_apply z
  have hRight : R.comp Ri = ContinuousLinearMap.id ℝ X := by
    apply ContinuousLinearMap.ext
    intro z
    exact e.apply_symm_apply z
  have hId : operatorMatrixMap (ContinuousLinearMap.id ℝ X) = (1:Mat) :=
    matrixOperatorAlgEquiv.symm.map_one
  constructor
  · change (operatorMatrixMap R).transpose*operatorMatrixMap R = 1
    rw [← hTranspose,← operatorMatrixMap_comp,hLeft,hId]
  · change operatorMatrixMap R*(operatorMatrixMap R).transpose = 1
    rw [← hTranspose,← operatorMatrixMap_comp,hRight,hId]

/-- The independently parametrized normalized coefficient has exactly the
    native rotated principal coefficient used by the angular derivative
    theorem. There is no extra density or radius term. -/
theorem normalFrameNormalizedCoefficient_coordinate_rotation (g g₁ : MetricField) (E : X × X → X)
    (y : X) (s : ℝ) (L : X →L[ℝ] X) (i j : I) (θ : ℝ) (z : X) :
    normalFrameNormalizedCoefficient g g₁ E
      ((y,(s,L.comp (coordinateRotationIsometry i j θ).toContinuousLinearEquiv.toContinuousLinearMap)),z) =
      coordinateRotationPrincipalFamily i j
        (fun p : ℝ × X => normalFrameNormalizedCoefficient g g₁ E ((y,(s,L)),p.2)) ((θ,0),z) := by
  let Q := coordinateRotationMatrix i j θ
  let G := normalFrameMetric g₁ E ((y,(s,L)),coordinateRotation i j θ z)
  have hMetric := normalFrameMetric_coordinate_rotation g₁ E y s L i j θ z
  have hOrth := coordinateRotationMatrix_orthogonal i j θ
  have hCoeff := density_inverse_orthogonal_conjugation Q G hOrth.1 hOrth.2
  let H := normalFrameMetric g₁ E
    ((y,(s,L.comp (coordinateRotationIsometry i j θ).toContinuousLinearEquiv.toContinuousLinearMap)),z)
  have hRaw : Real.sqrt H.det • H⁻¹ = Q.transpose*(Real.sqrt G.det • G⁻¹)*Q := by
    dsimp only [H]
    rw [hMetric]
    exact hCoeff
  let c := (firstMetricDensityFactor g g₁ y)⁻¹
  have hScale := congrArg (fun A : Mat => c • A) hRaw
  have hBase : normalFrameNormalizedCoefficient g g₁ E ((y,(s,L)),coordinateRotation i j θ z) =
      c • (Real.sqrt G.det • G⁻¹) := by
    ext k l
    rfl
  have hAt : normalFrameNormalizedCoefficient g g₁ E
      ((y,(s,L.comp (coordinateRotationIsometry i j θ).toContinuousLinearEquiv.toContinuousLinearMap)),z) =
      c • (Real.sqrt H.det • H⁻¹) := by
    ext k l
    rfl
  rw [hAt]
  change c • (Real.sqrt H.det • H⁻¹) =
    Q.transpose*normalFrameNormalizedCoefficient g g₁ E ((y,(s,L)),coordinateRotation i j θ z)*Q
  rw [hBase]
  simpa only [Matrix.mul_smul,Matrix.smul_mul] using hScale

end ShrinkingSpheres
