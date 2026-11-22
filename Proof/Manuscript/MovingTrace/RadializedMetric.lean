module

public import Proof.Manuscript.MovingTrace.ScaledPhysicalCollarOperator
public import Mathlib.Analysis.SpecialFunctions.SmoothTransition
public import Mathlib.Analysis.Calculus.ContDiff.Operations

@[expose] public section

noncomputable section
set_option maxHeartbeats 2600000

open CalderonN Set Matrix Filter
open scoped ContDiff InnerProductSpace Topology

namespace CalderonPaper

variable {d : ℕ} [NeZero d]

/-- Reflection that reverses the radial direction and fixes the tangent
plane to the Euclidean sphere through z. -/
def radialReflection (z : X d) : X d →L[ℝ] X d :=
  ContinuousLinearMap.id ℝ (X d) -
    (2 / ‖z‖^2) • (innerSL ℝ z).smulRight z

theorem radialReflection_apply (z v : X d) :
    radialReflection z v = v - (2 / ‖z‖^2 * ⟪z,v⟫_ℝ) • z := by
  simp [radialReflection,smul_smul]

theorem radialReflection_radial {z : X d} (hz : z ≠ 0) :
    radialReflection z z = -z := by
  rw [radialReflection_apply,real_inner_self_eq_norm_sq,div_mul_cancel₀ _
    (pow_ne_zero _ (norm_ne_zero_iff.mpr hz))]
  module

theorem radialReflection_tangent {z v : X d} (hv : ⟪z,v⟫_ℝ = 0) :
    radialReflection z v = v := by
  simp [radialReflection_apply,hv]

/-- The auxiliary metric agrees with the literal metric whenever the
radial line and its orthogonal plane are already metric orthogonal. -/
def radializedMetric (χ : X d → ℝ) (g : MetricField d) (z : X d) : Mat d :=
  let R := coordinateMatrix (radialReflection z)
  (1-χ z/2) • g z + (χ z/2) • (Rᵀ * g z * R)

theorem radializedMetric_posDef {χ : X d → ℝ} {g : MetricField d} {z : X d}
    (hχ : 0 ≤ χ z ∧ χ z ≤ 1) (hg : (g z).PosDef) :
    (radializedMetric χ g z).PosDef := by
  let R := coordinateMatrix (radialReflection z)
  have hR : (Rᵀ * g z * R).PosSemidef := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using hg.posSemidef.conjTranspose_mul_mul_same R
  exact (hg.smul (by linarith only [hχ.2])).add_posSemidef
    (hR.smul (by linarith only [hχ.1]))

private theorem metricPair_conjugate_real (g : MetricField d) (R : X d →L[ℝ] X d)
    (z u v : X d) :
    metricPair (fun _ => (coordinateMatrix R)ᵀ * g z * coordinateMatrix R) z u v =
      metricPair g z (R u) (R v) := by
  let e : Frame d := fun _ i => R (axis i)
  have hR (w : X d) : frameVector e z w = R w := by
    unfold frameVector
    simp only [e,← map_smul,← map_sum]
    apply congrArg R
    simpa only [EuclideanSpace.basisFun_repr,EuclideanSpace.basisFun_apply,axis]
      using (EuclideanSpace.basisFun (Fin d) ℝ).sum_repr w
  have hPair (i j : I d) :
      ((coordinateMatrix R)ᵀ * g z * coordinateMatrix R) i j =
      metricPair g z (R (axis i)) (R (axis j)) := by
    have h := pullbackMetric_entry_metricPair (fun _ => g z) R z i j
    simpa only [pullbackMetric,coordinateJacobian,R.fderiv,metricPair] using h
  rw [← hR u,← hR v,metricPair_frame_expansion]
  change (∑ i, ∑ j, ((coordinateMatrix R)ᵀ * g z * coordinateMatrix R) i j * u i * v j) = _
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  rw [hPair]

private theorem metricPair_add_left' (g : MetricField d) (z u v w : X d) :
    metricPair g z (u+v) w = metricPair g z u w + metricPair g z v w := by
  simp only [metricPair,PiLp.add_apply,mul_add,add_mul,Finset.sum_add_distrib]

private theorem metricPair_add_right' (g : MetricField d) (z u v w : X d) :
    metricPair g z u (v+w) = metricPair g z u v + metricPair g z u w := by
  simp only [metricPair,PiLp.add_apply,mul_add,Finset.sum_add_distrib]

theorem radializedMetric_metricPair (χ : X d → ℝ) (g : MetricField d) (z u v : X d) :
    metricPair (radializedMetric χ g) z u v =
      (1-χ z/2) * metricPair g z u v +
        (χ z/2) * metricPair g z (radialReflection z u) (radialReflection z v) := by
  rw [← metricPair_conjugate_real]
  unfold metricPair radializedMetric
  simp only [Matrix.add_apply,Matrix.smul_apply,smul_eq_mul,Finset.sum_add_distrib,
    Finset.mul_sum,mul_add,add_mul]
  congr 1 <;> apply Finset.sum_congr rfl <;> intro i hi <;> apply Finset.sum_congr rfl <;> intro j hj <;> ring

theorem radializedMetric_mixed_zero {χ : X d → ℝ} {g : MetricField d} {z v : X d}
    (hχ : χ z = 1) (hz : z ≠ 0) (hv : ⟪z,v⟫_ℝ = 0) :
    metricPair (radializedMetric χ g) z z v = 0 := by
  rw [radializedMetric_metricPair,hχ,radialReflection_radial hz,radialReflection_tangent hv,
    ← neg_one_smul ℝ z,metricPair_smul_left]
  ring

theorem radializedMetric_eq_at_zeroCutoff {χ : X d → ℝ} {g : MetricField d} {z : X d}
    (hχ : χ z = 0) : radializedMetric χ g z = g z := by
  simp [radializedMetric,hχ]

theorem radializedMetric_eq_of_gauss {χ : X d → ℝ} {g : MetricField d} {z : X d}
    (hz : z ≠ 0) (hG : (g z).IsSymm) (c : ℝ)
    (hGauss : ∀ v, metricPair g z z v = c * ⟪z,v⟫_ℝ) :
    radializedMetric χ g z = g z := by
  have hSame (u v : X d) :
      metricPair g z (radialReflection z u) (radialReflection z v) = metricPair g z u v := by
    let a := 2 / ‖z‖^2 * ⟪z,u⟫_ℝ
    let b := 2 / ‖z‖^2 * ⟪z,v⟫_ℝ
    rw [radialReflection_apply,radialReflection_apply]
    change metricPair g z (u-a • z) (v-b • z) = _
    simp only [sub_eq_add_neg,metricPair_add_left',metricPair_add_right']
    simp only [← neg_smul,metricPair_smul_left,metricPair_smul_right,hGauss]
    rw [metricPair_symm g z u z hG.eq,hGauss,real_inner_self_eq_norm_sq]
    unfold a b
    field_simp [norm_ne_zero_iff.mpr hz]
    <;> ring
  ext i j
  have h := radializedMetric_metricPair χ g z (axis i) (axis j)
  rw [hSame,← add_mul,sub_add_cancel,one_mul,metricPair_axis_left,metricPair_axis_left] at h
  simpa [axis] using h

end CalderonPaper
