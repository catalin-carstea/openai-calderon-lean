import Proof.MetricConnection

set_option maxSynthPendingDepth 10
noncomputable section
open Set
namespace ShrinkingSpheres

/-- The coordinate metric as a continuous bilinear form. -/
def metricBilinear (g : MetricField) (y : X) : X →L[ℝ] X →L[ℝ] ℝ :=
  ∑ i, ∑ j, (g y i j) • (EuclideanSpace.proj i).smulRight (EuclideanSpace.proj j)

lemma metricBilinear_apply (g : MetricField) (y u v : X) :
    metricBilinear g y u v = metricPair g y u v := by
  simp only [metricBilinear, _root_.sum_apply, _root_.smul_apply,
    ContinuousLinearMap.smulRight_apply, PiLp.proj_apply, smul_eq_mul, metricPair]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- The connection coefficients as a continuous bilinear map in its two vector arguments. -/
def connectionBilinear (g : MetricField) (y : X) : X →L[ℝ] X →L[ℝ] X :=
  ∑ i, ∑ j, ∑ k, (christoffel g y k i j) •
    (EuclideanSpace.proj i).smulRight ((EuclideanSpace.proj j).smulRight (axis k))

lemma connectionBilinear_apply (g : MetricField) (y a v : X) :
    connectionBilinear g y a v = connection g y a v := by
  ext l
  simp [connectionBilinear, connection, axis, smul_smul, Pi.single_apply]

/-- The spatial derivative of the metric with two fixed tangent vectors. -/
def metricDifferential (g : MetricField) (y : X) : X →L[ℝ] X →L[ℝ] X →L[ℝ] ℝ :=
  ∑ i, ∑ j, (fderiv ℝ (fun x => g x i j) y).smulRight
    ((EuclideanSpace.proj i).smulRight (EuclideanSpace.proj j))

lemma metricDifferential_apply (g : MetricField) (y a u v : X) :
    metricDifferential g y a u v = ∑ i, ∑ j, (fderiv ℝ (fun x => g x i j) y a) * u i * v j := by
  simp only [metricDifferential, _root_.sum_apply, ContinuousLinearMap.smulRight_apply,
    _root_.smul_apply, PiLp.proj_apply, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

lemma axis_expansion (v : X) : (∑ i, v i • axis i) = v := by
  simpa only [EuclideanSpace.basisFun_apply, EuclideanSpace.basisFun_repr, axis]
    using (EuclideanSpace.basisFun I ℝ).sum_repr v

lemma connection_metric_basis_direction {Ω : Set X} (hΩ : IsOpen Ω) {K : ℝ} {g : MetricField}
    (h : Elliptic Ω K g) (hK : 0 < K) {y : X} (hy : y ∈ Ω) (a : X) (i j : I) :
    metricPair g y (connection g y a (axis i)) (axis j) +
      metricPair g y (axis i) (connection g y a (axis j)) =
        fderiv ℝ (fun x => g x i j) y a := by
  have hsum := axis_expansion a
  rw [← connectionBilinear_apply, ← connectionBilinear_apply,
    ← metricBilinear_apply, ← metricBilinear_apply]
  rw [← hsum]
  simp only [map_sum, map_smul, _root_.sum_apply, _root_.smul_apply,
    smul_eq_mul]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro k _
  rw [← mul_add, metricBilinear_apply, metricBilinear_apply,
    connectionBilinear_apply, connectionBilinear_apply, connection_metric_basis hΩ h hK hy]
  rfl

/-- Full metric compatibility, in the same ambient tangent coordinates as horizontal. -/
lemma connection_metric {Ω : Set X} (hΩ : IsOpen Ω) {K : ℝ} {g : MetricField}
    (h : Elliptic Ω K g) (hK : 0 < K) {y : X} (hy : y ∈ Ω) (a u v : X) :
    metricPair g y (connection g y a u) v + metricPair g y u (connection g y a v) =
      metricDifferential g y a u v := by
  have basis (i j : I) :
      metricBilinear g y (connectionBilinear g y a (axis i)) (axis j) +
        metricBilinear g y (axis i) (connectionBilinear g y a (axis j)) =
          metricDifferential g y a (axis i) (axis j) := by
    rw [metricBilinear_apply, metricBilinear_apply,
      connectionBilinear_apply, connectionBilinear_apply, connection_metric_basis_direction hΩ h hK hy]
    simp [metricDifferential_apply, axis]
  rw [← connectionBilinear_apply, ← connectionBilinear_apply,
    ← metricBilinear_apply, ← metricBilinear_apply]
  rw [← axis_expansion u, ← axis_expansion v]
  simp only [map_sum, map_smul, _root_.sum_apply, _root_.smul_apply,
    smul_eq_mul, Finset.mul_sum]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  have hb := congrArg (fun z => v i * u j * z) (basis j i)
  nlinarith only [hb]

end ShrinkingSpheres
