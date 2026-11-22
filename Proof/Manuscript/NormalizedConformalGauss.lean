module

public import Proof.CalderonN.MovingBallFamilies
public import Proof.CalderonN.FirstMetricConformalFactor
public import Proof.CalderonN.GaussVelocityAdjoint

import Proof.CalderonN.FramedNormalRadialCoefficient
import Proof.CalderonN.NormalMapDerivativeTaylor
import Mathlib.Tactic

public section

noncomputable section

open Set Metric CalderonN Matrix
open scoped ContDiff InnerProductSpace

namespace CalderonPaper

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {dim : ℕ} [NeZero dim]

/-- The normalized fixed-ball metric and the framed normal pullback are
the same bilinear form on the admitted velocity disk. -/
theorem normalizedBallMetric_eq_framedNormalMetric_at
    {Y Ω : Set (X dim)} {γ g : MetricField dim} {E : X dim × X dim → X dim}
    {R : X dim → ℝ} (hN : NormalCoordinates Y Ω γ E R) {y : X dim} (hy : y ∈ Y)
    (e : Frame dim) (s : ℝ) {z : X dim}
    (hz : s • frameVector e y z ∈ disk γ y (R y)) :
    normalizedBallMetric g E e y s z = framedNormalMetric g e E y s z := by
  let p := E (y,s • frameVector e y z)
  let D := normalizedBallDerivative E e y s z
  have hD (i : I dim) : D (axis i) = fderiv ℝ E (y,s • frameVector e y z) (0,e y i) := by
    have hDiff := (hN.hasFDerivAt_velocity_slice hy (s • frameVector e y z) hz).fderiv
    simp only [D,normalizedBallDerivative,ContinuousLinearMap.comp_apply,frameVectorL_apply_frame,
      frameVector_axis,hDiff,normalVerticalJacobian,ContinuousLinearMap.inr_apply]
  ext i j
  change ((coordinateMatrix D)ᵀ * g p * coordinateMatrix D) i j =
    metricPair g p (fderiv ℝ E (y,s • frameVector e y z) (0,e y i))
      (fderiv ℝ E (y,s • frameVector e y z) (0,e y j))
  rw [← hD i,← hD j]
  simp only [metricPair,Matrix.mul_apply,Matrix.transpose_apply,← coordinateMatrix_apply,Finset.sum_mul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring

/-- In the conformal first metric the Euclidean radial line is an exact
eigenline at every admitted normalized coordinate, with the endpoint
conformal factor as its eigenvalue. -/
theorem normalized_conformalMetric_radial_eigenline
    {Y Ω : Set (X dim)} (hΩ : IsOpen Ω) {γ g q : MetricField dim} {K : ℝ}
    {m : ℕ} {B : Fin (m+1) → ℝ} {e : Frame dim}
    (hB : Background Ω K B γ g q e) (hK : 0 < K)
    {E : X dim × X dim → X dim} {R : X dim → ℝ} (hN : NormalCoordinates Y Ω γ E R)
    {y : X dim} (hy : y ∈ Y) {s : ℝ} (hs : s ≠ 0) {z : X dim}
    (hz : s • frameVector e y z ∈ interior (disk γ y (R y))) (u : X dim) :
    metricPair (normalizedBallMetric g E e y s) z z u =
      firstMetricConformalFactor γ g (normalBallChartMap E e y s z) * ⟪z,u⟫_ℝ := by
  let p := normalBallChartMap E e y s z
  let a := firstMetricConformalFactor γ g p
  let D := coordinateMatrix (normalizedBallDerivative E e y s z)
  have hp : p ∈ Ω := ((hN.2 y hy).2.2 _ (interior_subset hz)).1
  have hEq : normalizedBallMetric g E e y s z = a • normalizedBallMetric γ E e y s z := by
    change Dᵀ * g p * D = a • (Dᵀ * γ p * D)
    rw [hB.firstMetric_eq_conformalFactor hK hp, Matrix.mul_smul,Matrix.smul_mul]
  have hPair : metricPair (normalizedBallMetric g E e y s) z z u =
      a * metricPair (normalizedBallMetric γ E e y s) z z u := by
    calc
      _ = metricPair (fun x => a • normalizedBallMetric γ E e y s x) z z u := by
        simp only [metricPair,hEq]
      _ = _ := metricPair_smul_metric _ _ _ _ _
  rw [hPair, show metricPair (normalizedBallMetric γ E e y s) z z u =
      metricPair (framedNormalMetric γ e E y s) z z u by
    simp only [metricPair,normalizedBallMetric_eq_framedNormalMetric_at hN hy e s (interior_subset hz)]]
  rw [hN.framedNormalMetric_gauss hΩ hB.1 hK hy (hN.center_mem hy) e s hs z u hz,
    metricPair_frameVector _ _ _ _ _ (hB.2.2.2.2.2.2.2 y (hN.center_mem hy))]
  congr 1
  simp only [EuclideanSpace.inner_eq_star_dotProduct,star_trivial,dotProduct,mul_comm]

omit [NeZero dim] in
theorem normalizedBallMetric_isSymm_of_smoothMetric
    {g : MetricField dim} (hg : SmoothMetric univ g) (E : X dim × X dim → X dim)
    (e : Frame dim) (y : X dim) (s : ℝ) (z : X dim) :
    (normalizedBallMetric g E e y s z).IsSymm := by
  have hSym := (hg.2 _ (mem_univ (normalBallChartMap E e y s z))).isHermitian.isSymm.eq
  change ((coordinateMatrix (normalizedBallDerivative E e y s z))ᵀ *
    g (normalBallChartMap E e y s z) * coordinateMatrix (normalizedBallDerivative E e y s z))ᵀ = _
  rw [Matrix.transpose_mul,Matrix.transpose_mul,Matrix.transpose_transpose,hSym]
  simp only [normalizedBallMetric,Matrix.mul_assoc]

omit [NeZero dim] in
/-- The Gauss eigenline implies that the conormal is radial, and its
weight is the exact volume density divided by the radial metric entry. -/
theorem ballConormalVector_radial_of_radial_eigenline
    {g : MetricField dim} {z : X dim} {a : ℝ} (ha : a ≠ 0) (hg : (g z).PosDef)
    (hRad : ∀ u, metricPair g z z u = a * ⟪z,u⟫_ℝ) :
    ballConormalVector g z = (chartVolume g z / a) • z := by
  have hRow (j : I dim) : ∑ i, z i * g z i j = a * z j := by
    have h := hRad (axis j)
    simpa [metricPair,axis,EuclideanSpace.inner_eq_star_dotProduct,dotProduct,PiLp.single_apply,
      Pi.single_apply,mul_ite,ite_mul,mul_comm,mul_left_comm] using h
  have hM : Matrix.vecMul (fun i => z i) (g z) = a • (fun i => z i) := funext hRow
  have hInv := congrArg (fun w => Matrix.vecMul w (g z)⁻¹) hM
  rw [Matrix.vecMul_vecMul, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hg.det_pos.ne'),
    Matrix.vecMul_one, Matrix.smul_vecMul] at hInv
  ext j
  have h := congrFun hInv j
  change z j = a * ∑ i, z i * (g z)⁻¹ i j at h
  change (∑ i, z i * divergenceCoeff g z i j) = (chartVolume g z / a) * z j
  have hDist : (∑ i, z i * divergenceCoeff g z i j) =
      chartVolume g z * ∑ i, z i * (g z)⁻¹ i j := by
    simp only [divergenceCoeff,Finset.mul_sum]
    exact Finset.sum_congr rfl (fun i _ => by ring)
  rw [hDist,h]
  field_simp

/-- The conformal normalized metric preserves the Euclidean radial line
on the whole closed unit ball, including the zero-radius reference. -/
theorem normalizedBallMetric_radial_eigenline_on_closedBall
    {Y Ω : Set (X dim)} (hΩ : IsOpen Ω) {γ g q : MetricField dim} {K : ℝ}
    {m : ℕ} {B : Fin (m+1) → ℝ} {e : Frame dim}
    (hB : Background Ω K B γ g q e) (hK : 0 < K)
    {E : X dim × X dim → X dim} (hE : ContDiff ℝ ∞ E)
    {R : X dim → ℝ} (hN : NormalCoordinates Y Ω γ E R)
    {y : X dim} (hy : y ∈ Y) {s : ℝ} (hs : s ∈ Ico 0 (R y)) {z : X dim}
    (hz : z ∈ closedBall (0 : X dim) 1) :
    ∃ a > 0, ∀ u, metricPair (normalizedBallMetric g E e y s) z z u = a * ⟪z,u⟫_ℝ := by
  have hFrame := hB.2.2.2.2.2.2.2 y (hN.center_mem hy)
  rcases eq_or_lt_of_le hs.1 with hZero | hPos
  · obtain ⟨a,ha,he⟩ := hB.2.2.2.1 y (hN.center_mem hy)
    have hm : normalizedBallMetric g E e y s = fun _ => a⁻¹ • (1 : Mat dim) := by
      rw [← hZero]
      funext w
      exact normalizedBallMetric_zero_of_conformal hE hN hy hFrame ha he w
    refine ⟨a⁻¹,inv_pos.mpr ha,fun u => ?_⟩
    rw [hm,metricPair_smul_metric]
    congr 1
    simp [metricPair,Matrix.one_apply,EuclideanSpace.inner_eq_star_dotProduct,dotProduct,mul_comm]
  · have hz₁ : ‖z‖ ≤ 1 := mem_closedBall_zero_iff.mp hz
    have hDisk : s • frameVector e y z ∈ interior (disk γ y (R y)) := by
      apply mem_interior_disk_of_metricPair_lt
      rw [metricPair_scaled_frameVector _ _ _ hFrame]
      have hSq₁ : ‖z‖^2 ≤ 1 := pow_le_one₀ (norm_nonneg _) hz₁
      have hSq₂ : s^2 < (R y)^2 := (sq_lt_sq₀ hPos.le (hPos.trans hs.2).le).mpr hs.2
      exact (mul_le_of_le_one_right (sq_nonneg _) hSq₁).trans_lt hSq₂
    have hx : normalBallChartMap E e y s z ∈ Ω := ((hN.2 y hy).2.2 _ (interior_subset hDisk)).1
    exact ⟨_,hB.firstMetricConformalFactor_pos hK hx,fun u =>
      normalized_conformalMetric_radial_eigenline hΩ hB hK hN hy hPos.ne' hDisk u⟩

/-- Use the actual radial conormal scalar, divided by any fixed positive
center normalization, for the weight in the Gauss formula. -/
@[expose] def sphereGaussWeight (g : MetricField dim) (c : ℝ) (z : X dim) : ℝ :=
  ⟪z,ballConormalVector g z⟫_ℝ / c

theorem sphereGaussWeight_contDiffOn {g : MetricField dim} {U : Set (X dim)}
    (hg : SmoothMetric U g) (c : ℝ) : ContDiffOn ℝ ∞ (sphereGaussWeight g c) U :=
  (contDiffOn_id.inner ℝ (contDiffOn_ballConormalVector hg)).div_const c

theorem sphereGaussWeight_pos {g : MetricField dim} {c : ℝ} (hc : 0 < c)
    {z : X dim} (hg : (g z).PosDef) (hz : z ≠ 0) : 0 < sphereGaussWeight g c z :=
  div_pos (ballConormalVector_inner_pos hg hz) hc

theorem ballConormalVector_eq_sphereGaussWeight_smul
    {g : MetricField dim} {c : ℝ} (hc : c ≠ 0) {z : X dim} (hz : z ∈ standardSphere dim)
    (hg : (g z).PosDef) {a : ℝ} (ha : a ≠ 0)
    (hRad : ∀ u, metricPair g z z u = a * ⟪z,u⟫_ℝ) :
    ballConormalVector g z = (c * sphereGaussWeight g c z) • z := by
  have hRadial := ballConormalVector_radial_of_radial_eigenline ha hg hRad
  conv_rhs => rw [sphereGaussWeight,hRadial,real_inner_smul_right,real_inner_self_eq_norm_sq,
    mem_sphere_zero_iff_norm.mp hz,one_pow,mul_one,← mul_div_assoc,mul_div_cancel_left₀ _ hc]
  exact hRadial

end CalderonPaper
