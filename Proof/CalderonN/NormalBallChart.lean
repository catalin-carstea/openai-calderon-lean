module

public import Proof.CalderonN.MovingCutoffGeometry
public import Proof.CalderonN.FrameOperators
public import Proof.CalderonN.LinearMetric

import Proof.CalderonN.MetricPair
import Mathlib.Tactic

@[expose] public section

noncomputable section
open Set Metric
open scoped ContDiff

namespace CalderonN

variable {dim : ℕ} [NeZero dim]

/-- Rescale the literal reference-metric normal ball to the fixed
Euclidean unit ball. The derivative includes the physical radius. -/
@[expose] def normalBallChartMap (E : (X dim) × (X dim) → (X dim)) (e : (Frame dim)) (y : (X dim)) (r : ℝ) (z : (X dim)) : (X dim) :=
  E (y,r • frameVector e y z)

theorem frameVectorL_apply_frame (e : Frame dim) (y z : X dim) :
    frameVectorL (e y) z = frameVector e y z := by
  rw [frameVectorL_apply (e y) z y]
  rfl

theorem contDiff_normalBallChartMap {E : (X dim) × (X dim) → (X dim)} (hE : ContDiff ℝ ∞ E)
    (e : (Frame dim)) (y : (X dim)) (r : ℝ) : ContDiff ℝ ∞ (normalBallChartMap E e y r) := by
  unfold normalBallChartMap
  simp_rw [← frameVectorL_apply_frame]
  exact hE.comp (contDiff_const.prodMk ((r • frameVectorL (e y)).contDiff))

theorem metricPair_scaled_frameVector (γ : (MetricField dim)) (e : (Frame dim)) (y : (X dim))
    (he : ∀ i j, metricPair γ y (e y i) (e y j) = if i = j then 1 else 0) (r : ℝ) (z : (X dim)) :
    metricPair γ y (r • frameVector e y z) (r • frameVector e y z) = r^2 * ‖z‖^2 := by
  rw [metricPair_smul_same, metricPair_frameVector γ e y z z he, EuclideanSpace.real_norm_sq_eq]
  simp only [pow_two]

theorem normalBallChartMap_deriv {E : (X dim) × (X dim) → (X dim)} (hE : ContDiff ℝ ∞ E)
    (e : (Frame dim)) (y : (X dim)) (r : ℝ) (z : (X dim)) :
    fderiv ℝ (normalBallChartMap E e y r) z =
      (fderiv ℝ (fun w => E (y,w)) (r • frameVector e y z)).comp (r • frameVectorL (e y)) := by
  unfold normalBallChartMap
  simp_rw [← frameVectorL_apply_frame]
  have h := (hE.comp (contDiff_const.prodMk contDiff_id) :
    ContDiff ℝ ∞ (fun w => E (y,w))).differentiable (by simp) (r • frameVectorL (e y) z)
  exact (h.hasFDerivAt.comp z (r • frameVectorL (e y)).hasFDerivAt).fderiv

private theorem bijective_scaled_frameVectorL (γ : (MetricField dim)) (e : (Frame dim)) (y : (X dim))
    (he : ∀ i j, metricPair γ y (e y i) (e y j) = if i = j then 1 else 0)
    {r : ℝ} (hr : r ≠ 0) : Function.Bijective (r • frameVectorL (e y)) := by
  let A := r • frameVectorL (e y)
  let B := r⁻¹ • frameCoordinatesL γ y (e y)
  have hAB (z : (X dim)) : A (B z) = z := by
    change r • frameVectorL (e y) (r⁻¹ • frameCoordinatesL γ y (e y) z) = z
    rw [map_smul,smul_inv_smul₀ hr,frameVectorL_frameCoordinatesL γ y (e y) he]
  have hBA (z : (X dim)) : B (A z) = z := by
    change r⁻¹ • frameCoordinatesL γ y (e y) (r • frameVectorL (e y) z) = z
    rw [map_smul,inv_smul_smul₀ hr,frameCoordinatesL_frameVectorL γ y (e y) he]
  exact ⟨Function.LeftInverse.injective hBA,Function.RightInverse.surjective hAB⟩

/-- On the full rescaled open normal disk, the unit-ball chart is
injective, has invertible derivative, and lies in the physical chart. -/
theorem normalBallChartMap_on_openBall
    {Y Ω : Set (X dim)} {γ : (MetricField dim)} {ρ : ℝ} {E : (X dim) × (X dim) → (X dim)}
    (hE : ContDiff ℝ ∞ E) (hN : NormalCoordinates Y Ω γ E (fun _ => ρ))
    {e : (Frame dim)} {y : (X dim)} (hy : y ∈ Y)
    (he : ∀ i j, metricPair γ y (e y i) (e y j) = if i = j then 1 else 0)
    {r : ℝ} (hr : 0 < r) :
    let U := ball (0 : (X dim)) (ρ/r)
    let F := normalBallChartMap E e y r
    InjOn F U ∧ MapsTo F U Ω ∧ ∀ z ∈ U, Function.Bijective (fderiv ℝ F z) := by
  let U := ball (0 : (X dim)) (ρ/r)
  let A := r • frameVectorL (e y)
  have hA : Function.Bijective A := bijective_scaled_frameVectorL γ e y he hr.ne'
  have hAmap (z : (X dim)) (hz : z ∈ U) : r • frameVector e y z ∈ disk γ y ρ := by
    have hz' := (lt_div_iff₀ hr).mp (mem_ball_zero_iff.mp hz)
    have hSq := pow_le_pow_left₀ (show 0 ≤ ‖z‖*r from mul_nonneg (norm_nonneg _) hr.le) hz'.le 2
    change metricPair γ y (r • frameVector e y z) (r • frameVector e y z) ≤ ρ^2
    rw [metricPair_scaled_frameVector γ e y he]
    simpa only [mul_pow,mul_comm] using hSq
  refine ⟨?_,fun z hz => ((hN.2 y hy).2.2 _ (hAmap z hz)).1,?_⟩
  · intro z hz w hw heq
    apply hA.1
    simpa only [A, ContinuousLinearMap.smul_apply, frameVectorL_apply_frame] using
      (hN.2 y hy).2.1 (hAmap z hz) (hAmap w hw) heq
  · intro z hz
    rw [normalBallChartMap_deriv hE]
    exact (((hN.2 y hy).2.2 _ (hAmap z hz)).2.1).comp hA

theorem normalBallChartMap_image_unitBall
    {Y : Set (X dim)} {γ : (MetricField dim)} {ρ : ℝ} {E V : (X dim) × (X dim) → (X dim)}
    (hExact : ∀ z ∈ normalVelocityDomain Y γ ρ, V (E z,z.1) = z.2)
    (hInv : ∀ q ∈ normalPairDomain Y γ ρ E,
      (q.2,V q) ∈ normalVelocityDomain Y γ ρ ∧ E (q.2,V q) = q.1)
    {e : (Frame dim)} {y : (X dim)} (hy : y ∈ Y)
    (he : ∀ i j, metricPair γ y (e y i) (e y j) = if i = j then 1 else 0)
    {r : ℝ} (hr : 0 < r) (hCap : r < ρ) :
    normalBallChartMap E e y r '' ball (0 : (X dim)) 1 =
      normalBallRoom (normalPairDomain Y γ ρ E) γ V y r := by
  ext x
  constructor
  · rintro ⟨z,hz,rfl⟩
    let v := r • frameVector e y z
    have hRad : metricPair γ y v v < r^2 := by
      dsimp only [v]
      rw [metricPair_scaled_frameVector γ e y he]
      have hsq := pow_lt_pow_left₀ (mem_ball_zero_iff.mp hz) (norm_nonneg _) (by decide : 2 ≠ 0)
      nlinarith only [mul_lt_mul_of_pos_left hsq (sq_pos_of_pos hr)]
    have hVel : (y,v) ∈ normalVelocityDomain Y γ ρ :=
      ⟨hy,hRad.trans (pow_lt_pow_left₀ hCap hr.le (by decide))⟩
    refine ⟨⟨(y,v),hVel,rfl⟩,?_⟩
    change metricPair γ y (V (E (y,v),y)) (V (E (y,v),y)) < r^2
    rw [hExact (y,v) hVel]
    exact hRad
  · rintro ⟨hpair,hRad⟩
    let v := V (x,y)
    let w := frameCoordinates γ y (e y) v
    let z := r⁻¹ • w
    have hSq : ‖w‖^2 < r^2 := (norm_frameCoordinates_sq γ y v (e y) he).trans_lt hRad
    have hlt : ‖w‖ < r := (sq_lt_sq₀ (norm_nonneg _) hr.le).mp hSq
    have hz : z ∈ ball (0 : (X dim)) 1 := by
      rw [mem_ball_zero_iff,norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hr)]
      exact (inv_mul_lt_iff₀ hr).mpr (by simpa using hlt)
    refine ⟨z,hz,?_⟩
    have hw : frameVector e y z = r⁻¹ • v := by
      rw [← frameVectorL_apply_frame, show z = r⁻¹ • w from rfl, map_smul,
        frameVectorL_apply _ _ y, frameVector_frameCoordinates _ _ _ _ he]
    rw [normalBallChartMap,hw,smul_inv_smul₀ hr.ne']
    exact (hInv (x,y) hpair).2

end CalderonN
