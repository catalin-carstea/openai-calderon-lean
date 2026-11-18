import Proof.NormalChart
import Proof.LocalMetricPullbackDivergence

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 700000
set_option maxSynthPendingDepth 15
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Matrix
open scoped ContDiff Matrix.Norms.Elementwise
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon
open OAI.AnisotropicCalderon.MetricOperator OAI.AnisotropicCalderon.ConnectionError

lemma NormalCoordinates.normalChart_jacobian_isUnit {Y Ω : Set X} {γ : MetricField}
    {expMap : X × X → X} {R : X → ℝ}
    (hN : NormalCoordinates Y Ω γ expMap R) {y : X} (hy : y ∈ Y) (e : Frame)
    (hFrame : ∀ i j,metricPair γ y (e y i) (e y j) = if i=j then 1 else 0)
    (r : ℝ) (hr : 0 < r) (z : X) (hv : r • frameVector e y z ∈ disk γ y (R y)) :
    IsUnit (coordinateJacobianMatrix (normalChart expMap e y r) z).det := by
  have hBij := hN.normalChart_derivative_bijective hy e hFrame r hr z hv
  have hUnit : IsUnit (fderiv ℝ (normalChart expMap e y r) z) :=
    ContinuousLinearMap.isUnit_iff_bijective.mpr hBij
  apply (Matrix.isUnit_iff_isUnit_det _).mp
  rw [coordinateJacobianMatrix_eq_operatorMatrixMap]
  change IsUnit (matrixOperatorAlgEquiv.symm (fderiv ℝ (normalChart expMap e y r) z))
  exact hUnit.map matrixOperatorAlgEquiv.symm.toMonoidHom

lemma pullbackMetric_entry (g : MetricField) (F : X → X) (z : X) (i j : I) :
    pullbackMetric g F z i j = metricPair g (F z)
      (fderiv ℝ F z (axis i)) (fderiv ℝ F z (axis j)) := by
  have hCoord (a b : I) : operatorMatrixMap (fderiv ℝ F z) a b = (fderiv ℝ F z (axis b)) a := by
    rw [← coordinateJacobianMatrix_eq_operatorMatrixMap]
    rfl
  have hP : pullbackMetric g F z = (operatorMatrixMap (fderiv ℝ F z))ᵀ*g (F z)*operatorMatrixMap (fderiv ℝ F z) := by
    simp only [pullbackMetric,operatorMatrixMap_comp,operatorMatrixMap_adjoint,
      operatorMatrixMap_metricOperatorField,Matrix.mul_assoc]
  rw [hP]
  simp only [Matrix.mul_apply,Matrix.transpose_apply,Finset.sum_mul,hCoord,metricPair]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro b hb
  ring

/-- The full physical chart pullback is exactly the radius squared times the
    actual normalized framed metric used by the fixed-ball PDE theory. -/
theorem NormalCoordinates.normalChart_pullbackMetric {Y Ω : Set X} {γ : MetricField}
    {expMap : X × X → X} {R : X → ℝ}
    (hN : NormalCoordinates Y Ω γ expMap R) {y : X} (hy : y ∈ Y) (g : MetricField) (e : Frame)
    (r : ℝ) (z : X) (hv : r • frameVector e y z ∈ disk γ y (R y)) :
    pullbackMetric g (normalChart expMap e y r) z = r^2 • framedNormalMetric g e expMap y r z := by
  have hDF (a : I) : fderiv ℝ (normalChart expMap e y r) z (axis a) =
      r • normalVerticalJacobian expMap y (r • frameVector e y z) (e y a) := by
    rw [(hN.hasFDerivAt_normalChart hy e r z hv).fderiv,ContinuousLinearMap.comp_apply,
      _root_.smul_apply,frameVectorLinear_apply,frameVector_axis,map_smul]
  have hFramed (i j : I) : framedNormalMetric g e expMap y r z i j =
      metricPair g (normalChart expMap e y r z)
        (normalVerticalJacobian expMap y (r • frameVector e y z) (e y i))
        (normalVerticalJacobian expMap y (r • frameVector e y z) (e y j)) := rfl
  ext i j
  rw [pullbackMetric_entry,hDF i,hDF j,metricPair_smul_left,metricPair_smul_right]
  simp only [Matrix.smul_apply,smul_eq_mul,hFramed]
  ring

end ShrinkingSpheres
