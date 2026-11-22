module

public import Proof.CalderonN.NormalCoefficientVelocityJets
public import Proof.CalderonN.NormalBallHarmonic
public import Proof.CalderonN.MetricBallDirichlet

import Proof.CalderonN.NormalizedBallMetric
import Proof.CalderonN.NormalDivergenceScale
import Proof.CalderonN.GreenSourceCutoff
import Proof.CalderonN.HarmonicL2Space
import Mathlib.Tactic

public section

noncomputable section
open Set Filter Metric
open scoped ContDiff Topology Matrix.Norms.Elementwise
set_option maxHeartbeats 2700000
set_option maxSynthPendingDepth 25
set_option backward.isDefEq.respectTransparency false

namespace CalderonN

variable {dim : ℕ} [NeZero dim] [Nontrivial (Fin dim)]

omit [Nontrivial (Fin dim)] in
private theorem normalizedBallDerivative_eq_vertical (d : Data dim) (hE : ContDiff ℝ ∞ d.expMap)
    (y z : X dim) (r : ℝ) :
    normalizedBallDerivative d.expMap d.frame y r z =
      (normalVerticalJacobian d.expMap y (r • frameVector d.frame y z)).comp (frameVectorLinear d.frame y) := by
  let v := r • frameVector d.frame y z
  have h := ((hE.differentiable (by simp) (y,v)).hasFDerivAt.comp v
    (hasFDerivAt_prodMk_right y v)).fderiv
  change (fderiv ℝ (d.expMap ∘ Prod.mk y) v).comp (frameVectorL (d.frame y)) = _
  rw [h]
  rfl

/-- The actual normalized coefficient is a fixed positive scalar times the
physical pullback coefficient on the same ball. -/
theorem normalizedFirstCoefficient_eq_scaled_ballDivergence (hn : 2 ≤ dim)
    (d : Data dim) (hE : ContDiff ℝ ∞ d.expMap) (y : X dim) (r : ℝ) (hr : 0 < r)
    (z : X dim) (hPos : (pullbackMetric d.g₁ (normalBallChartMap d.expMap d.frame y r) z).PosDef) :
    firstNormalVelocityCoefficient d y (r • frameVector d.frame y z) =
      ((firstMetricDensityFactor d.γ d.g₁ y)⁻¹ * (r^(dim-2))⁻¹) •
        (fun i j => divergenceCoeff (pullbackMetric d.g₁
          (normalBallChartMap d.expMap d.frame y r)) z i j : Mat dim) := by
  let F := normalBallChartMap d.expMap d.frame y r
  let g := normalizedBallMetric d.g₁ d.expMap d.frame y r
  have h := pullbackMetric_normalBallChartMap hE d.g₁ d.frame y r
  have hPt : pullbackMetric d.g₁ F z = r^2 • g z := congrFun h z
  have hDet : IsUnit (g z).det := by
    apply isUnit_iff_ne_zero.mpr
    intro hZ
    have hP := hPos.det_pos
    change 0 < (pullbackMetric d.g₁ F z).det at hP
    rw [hPt,Matrix.det_smul,hZ,mul_zero] at hP
    exact (lt_irrefl 0) hP
  have hDiv (i j : I dim) : divergenceCoeff (pullbackMetric d.g₁ F) z i j =
      r^(dim-2) * divergenceCoeff g z i j := by
    change divergenceCoeff (pullbackMetric d.g₁ (normalBallChartMap d.expMap d.frame y r)) z i j = _
    rw [h]
    exact divergenceCoeff_scale_sq hn g r hr z hDet i j
  have hg : pullbackMetricMatrix (d.g₁ (d.expMap (y,r • frameVector d.frame y z)),
      (normalVerticalJacobian d.expMap y (r • frameVector d.frame y z)).comp (frameVectorLinear d.frame y)) = g z := by
    rw [← normalizedBallDerivative_eq_vertical d hE y z r]
    rfl
  ext i j
  change firstNormalVelocityCoefficient d y (r • frameVector d.frame y z) i j =
    ((firstMetricDensityFactor d.γ d.g₁ y)⁻¹ * (r^(dim-2))⁻¹) * divergenceCoeff (pullbackMetric d.g₁ F) z i j
  rw [firstNormalVelocityCoefficient,pullbackDivergenceMatrix,hg,hDiv]
  simp only [Matrix.smul_apply,smul_eq_mul,divergenceCoeff,chartVolume]
  field_simp [hr.ne']

omit [Nontrivial (Fin dim)] in
private theorem negativeBallDivergence_const_smul_metric {U : Set (X dim)} (hU : IsOpen U)
    {g : MetricField dim} (hg : SmoothMetric U g) (b : X dim → ℝ) (hb : ContDiff ℝ ∞ b)
    (c : ℝ) {z : X dim} (hz : z ∈ U) :
    negativeBallDivergence (fun w => c • (fun i j => divergenceCoeff g w i j : Mat dim)) b z =
      c * negativeBallDivergence (fun w => (fun i j => divergenceCoeff g w i j : Mat dim)) b z := by
  unfold negativeBallDivergence Elliptic.Lop
  have he (i : I dim) :
      (fun w => ∑ j, (c • (fun a b => divergenceCoeff g w a b : Mat dim)) i j * coordDeriv j b w) =
        fun w => c * divergenceFlux g b w i := by
    funext w
    change (∑ j, (c * divergenceCoeff g w i j) * coordDeriv j b w) = _
    simp only [divergenceFlux,Finset.mul_sum,mul_assoc]
  simp_rw [he]
  have hDer (i : I dim) :
      Elliptic.pd i (fun w => c * divergenceFlux g b w i) z =
        c * Elliptic.pd i (fun w => divergenceFlux g b w i) z := by
    have hs := ((contDiffOn_divergenceFlux hU hg hb.contDiffOn i).differentiableOn
      (by simp)).differentiableAt (hU.mem_nhds hz)
    change fderiv ℝ (c • (fun w => divergenceFlux g b w i)) z (axis i) = _
    rw [fderiv_const_smul hs c]
    rfl
  simp_rw [hDer]
  change -(∑ i, c * Elliptic.pd i (fun w => divergenceFlux g b w i) z) =
    c * (-(∑ i, Elliptic.pd i (fun w => divergenceFlux g b w i) z))
  rw [← Finset.mul_sum]
  ring

/-- The solution used in the normalized operator estimate agrees on the
closed ball with any physical first-metric solution of the same trace. -/
theorem eqOn_actualNormalPoisson_of_trace (hn : 2 ≤ dim)
    (d : Data dim) (hE : ContDiff ℝ ∞ d.expMap) (y : X dim) (hr : 0 < d.radius y)
    {U : Set (X dim)} (hU : IsOpen U) (hC : closedBall (0 : X dim) 1 ⊆ U)
    (hg : SmoothMetric U (pullbackMetric d.g₁ (normalBallChartMap d.expMap d.frame y (d.radius y))))
    {b u : X dim → ℝ} (hb : ContDiff ℝ ∞ b)
    (hP : EqOn (negativeBallDivergence (fun z =>
      firstNormalVelocityCoefficient d y (d.radius y • frameVector d.frame y z)) b) 0
      (ball (0 : X dim) 1))
    (hu : ContDiffOn ℝ ∞ (u ∘ normalBallChartMap d.expMap d.frame y (d.radius y)) U)
    (hH : EqOn (laplace (pullbackMetric d.g₁ (normalBallChartMap d.expMap d.frame y (d.radius y)))
      (u ∘ normalBallChartMap d.expMap d.frame y (d.radius y))) 0 (ball (0 : X dim) 1))
    (hT : EqOn b (u ∘ normalBallChartMap d.expMap d.frame y (d.radius y)) (standardSphere dim)) :
    let F := normalBallChartMap d.expMap d.frame y (d.radius y)
    EqOn b (u ∘ F) (closedBall (0 : X dim) 1) ∧
      EqOn (fun z => fderiv ℝ b z z) (fun z => fderiv ℝ (u ∘ F) z z) (standardSphere dim) := by
  let r := d.radius y
  let F := normalBallChartMap d.expMap d.frame y r
  let g := pullbackMetric d.g₁ F
  let c := (firstMetricDensityFactor d.γ d.g₁ y)⁻¹*(r^(dim-2))⁻¹
  have hc : c ≠ 0 := (mul_pos (inv_pos.mpr (firstMetricDensityFactor_pos _ _ _))
    (inv_pos.mpr (pow_pos hr _))).ne'
  have hLap (z : X dim) (hz : z ∈ ball (0 : X dim) 1) : laplace g b z = 0 := by
    have hz' := hC (ball_subset_closedBall hz)
    have hA : (fun w => firstNormalVelocityCoefficient d y (r • frameVector d.frame y w)) =ᶠ[𝓝 z]
        fun w => c • (fun i j => divergenceCoeff g w i j : Mat dim) := by
      filter_upwards [hU.mem_nhds hz'] with w hw
      exact normalizedFirstCoefficient_eq_scaled_ballDivergence hn d hE y r hr w (hg.2 w hw)
    have he := hP hz
    change negativeBallDivergence (fun w => firstNormalVelocityCoefficient d y
      (r • frameVector d.frame y w)) b z = 0 at he
    rw [negativeBallDivergence_congr_germ hA EventuallyEq.rfl,
      negativeBallDivergence_const_smul_metric hU hg b hb c hz',
      negativeBallDivergence_eq_neg_laplace_density hU hg hb hz' EventuallyEq.rfl] at he
    have hv : chartVolume g z ≠ 0 := (Real.sqrt_pos.2 (hg.2 z hz').det_pos).ne'
    exact neg_eq_zero.mp ((mul_eq_zero.mp ((mul_eq_zero.mp he).resolve_left hc)).resolve_right hv)
  have hu' : ContDiffOn ℝ ∞ (u ∘ F) U := hu
  have h := eqOn_closedUnitBall_of_laplace_eq_zero hU hC hg (hb.contDiffOn.sub hu')
    (u := b-u ∘ F)
    (fun z hz => by
      change laplace g (fun w => b w-(u ∘ F) w) z = 0
      have he : laplace g (u ∘ F) z = 0 := hH hz
      rw [laplace_sub hU g hb.contDiffOn hu' (hC (ball_subset_closedBall hz)),hLap z hz,he,sub_self])
    (fun z hz => sub_eq_zero.mpr (hT hz))
  have hEq : EqOn b (u ∘ F) (closedBall (0 : X dim) 1) := fun z hz => sub_eq_zero.mp (h hz)
  refine ⟨hEq,?_⟩
  intro z hz
  have hzB : z ∈ closedBall (0 : X dim) 1 := sphere_subset_closedBall hz
  have hUnique : UniqueDiffWithinAt ℝ (closedBall (0 : X dim) 1) z :=
    (uniqueDiffOn_convex (convex_closedBall _ _) (by
      rw [interior_closedBall _ one_ne_zero]
      exact ⟨0,mem_ball_self one_pos⟩)) z hzB
  have hUderiv := (hu'.differentiableOn (by simp)).differentiableAt (hU.mem_nhds (hC hzB))
  have he : fderiv ℝ b z = fderiv ℝ (u ∘ F) z := by
    rw [← ((hb.differentiable (by simp) z).hasFDerivAt.hasFDerivWithinAt).fderivWithin hUnique,
      ← (hUderiv.hasFDerivAt.hasFDerivWithinAt).fderivWithin hUnique]
    exact fderivWithin_congr hEq (hEq hzB)
  exact congrArg (fun L : X dim →L[ℝ] ℝ => L z) he

end CalderonN
