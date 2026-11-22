module

public import Proof.CalderonN.AdmittedGaussRadialAdjoint
public import Proof.CalderonN.SmoothStrongBallEstimates

import Proof.CalderonN.GreenSourceCutoff
import Proof.CalderonN.NormalMapDerivativeTaylor
import Mathlib.Tactic

/-! On the admitted chart, the normalized divergence coefficient and
the metric Laplacian specify the same classical solution. -/

public section

noncomputable section
open Set Filter Metric
open scoped ContDiff Topology Matrix.Norms.Elementwise
set_option autoImplicit false
set_option maxHeartbeats 3200000
set_option backward.isDefEq.respectTransparency false
namespace CalderonN
 
open BallDirichlet

variable {dim : ℕ} [NeZero dim] [Nontrivial (Fin dim)]

theorem admitted_normalBallDivergence_eq_scaled
    {Y Ω : Set (X dim)} {m : ℕ} {K ρ c₀ floor ε : ℝ} {M : Fin (m+1) → ℝ}
    {Cj : Fin 9 → ℝ} {d : Data dim} (hd : Admissible Y Ω K ρ c₀ M Cj floor ε d)
    {y : X dim} (hy : y ∈ Y) (hrρ : 2*d.radius y < ρ) :
    let r := d.radius y
    let a (z : X dim) := firstNormalVelocityCoefficient d y (r • frameVector d.frame y z)
    let g := normalizedBallMetric d.g₁ d.expMap d.frame y r
    let c := firstMetricDensityFactor d.γ d.g₁ y
    EqOn (fun z => (fun i j => divergenceCoeff g z i j : Mat dim)) (c • a) (ball (0 : X dim) 2) := by
  dsimp only
  let r := d.radius y
  let a (z : X dim) := firstNormalVelocityCoefficient d y (r • frameVector d.frame y z)
  let g := normalizedBallMetric d.g₁ d.expMap d.frame y r
  let c := firstMetricDensityFactor d.γ d.g₁ y
  have hc := (firstMetricDensityFactor_pos d.γ d.g₁ y).ne'
  have hr := (hd.2.2.2.2.1.2 y hy).1
  have he := hd.1.2.2.2.2.2.2.2 y (hd.2.1.center_mem hy)
  intro z hz
  let v := r • frameVector d.frame y z
  let D := (normalVerticalJacobian d.expMap y v).comp (frameVectorLinear d.frame y)
  have hL : frameVectorL (d.frame y) = frameVectorLinear d.frame y := by
    ext1 w
    rw [frameVectorL_apply_frame,frameVectorLinear_apply]
  have hIn : v ∈ interior (disk d.γ y (max ρ r)) := by
    apply mem_interior_disk_of_metricPair_lt
    change metricPair d.γ y (r • frameVector d.frame y z) (r • frameVector d.frame y z) < _
    rw [metricPair_scaled_frameVector d.γ d.frame y he]
    have h := mem_ball_zero_iff.mp hz
    have hb : r*‖z‖ < max ρ r :=
      ((mul_lt_mul_of_pos_left h hr).trans (mul_comm r 2 ▸ hrρ)).trans_le (le_max_left _ _)
    have hh := (sq_lt_sq₀ (mul_nonneg hr.le (norm_nonneg _)) (hr.le.trans (le_max_right _ _))).2 hb
    rwa [mul_pow] at hh
  have hD : normalizedBallDerivative d.expMap d.frame y r z = D := by
    unfold normalizedBallDerivative
    rw [hL]
    have h := (hd.2.1.hasFDerivAt_velocity_slice hy v (interior_subset hIn)).fderiv
    change fderiv ℝ (fun v => d.expMap (y,v)) (r • frameVector d.frame y z) = _ at h
    rw [h]
  have hm : g z = pullbackMetricMatrix (d.g₁ (d.expMap (y,v)),D) := by
    unfold g normalizedBallMetric pullbackMetricMatrix normalBallChartMap
    rw [hD]
  ext i j
  change divergenceCoeff g z i j =
    c*((c⁻¹ • pullbackDivergenceMatrix (d.g₁ (d.expMap (y,v)),D)) i j)
  rw [pullbackDivergenceMatrix,← hm,Matrix.smul_apply,smul_eq_mul,← mul_assoc,mul_inv_cancel₀ hc,one_mul]
  rfl

theorem admitted_fixedBallSolution_iff_normalDivergence
    {Y Ω : Set (X dim)} (hΩ : IsOpen Ω) {m : ℕ} {K ρ c₀ floor ε : ℝ}
    {M : Fin (m+1) → ℝ} {Cj : Fin 9 → ℝ} {d : Data dim}
    (hd : Admissible Y Ω K ρ c₀ M Cj floor ε d) (hK : 0 < K)
    {y : X dim} (hy : y ∈ Y) (hrρ : 2*d.radius y < ρ) (u : SmoothData dim) (f : X dim → ℝ) :
    let r := d.radius y
    let a (z : X dim) := firstNormalVelocityCoefficient d y (r • frameVector d.frame y z)
    FixedBallSolution (normalizedBallMetric d.g₁ d.expMap d.frame y r) f u.1 ↔
      EqOn u.1 f (standardSphere dim) ∧ EqOn (negativeBallDivergence a u.1) 0 (ball (0 : X dim) 1) := by
  dsimp only
  let r := d.radius y
  let a (z : X dim) := firstNormalVelocityCoefficient d y (r • frameVector d.frame y z)
  let g := normalizedBallMetric d.g₁ d.expMap d.frame y r
  let c := firstMetricDensityFactor d.γ d.g₁ y
  have hc : c ≠ 0 := (firstMetricDensityFactor_pos _ _ _).ne'
  obtain ⟨U,hU,hCU,hg⟩ := exists_admitted_normalizedBallMetric_smooth hΩ hd hK hy hrρ
  have hEq (z : X dim) (hz : z ∈ ball (0 : X dim) 1) :
      c*negativeBallDivergence a u.1 z = -(laplace g u.1 z)*chartVolume g z := by
    rw [← negativeBallDivergence_const_smul_coefficient]
    apply negativeBallDivergence_eq_neg_laplace_density hU hg u.2 (hCU (ball_subset_closedBall hz))
    have h := admitted_normalBallDivergence_eq_scaled hd hy hrρ
    filter_upwards [isOpen_ball.mem_nhds (ball_subset_ball (by norm_num : (1:ℝ) ≤ 2) hz)]
      with x hx using (h hx).symm
  constructor
  · rintro ⟨_,huT,huH⟩
    refine ⟨huT,fun z hz => ?_⟩
    have he := hEq z hz
    rw [huH z hz,neg_zero,zero_mul] at he
    exact (mul_eq_zero.mp he).resolve_left hc
  · rintro ⟨huT,huH⟩
    refine ⟨u.2,huT,fun z hz => ?_⟩
    have hV : chartVolume g z ≠ 0 := (Real.sqrt_pos.2 (hg.2 z (hCU (ball_subset_closedBall hz))).det_pos).ne'
    have he := hEq z hz
    have hZ : negativeBallDivergence a u.1 z = 0 := huH hz
    rw [hZ, mul_zero] at he
    exact neg_eq_zero.mp ((mul_eq_zero.mp he.symm).resolve_right hV)

end CalderonN
