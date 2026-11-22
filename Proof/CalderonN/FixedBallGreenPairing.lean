module

public import Proof.CalderonN.BallGreenIdentity
public import Proof.CalderonN.MetricPullback

import Mathlib.Tactic

@[expose] public section

noncomputable section
open Filter Set Metric MeasureTheory
open scoped ContDiff Topology InnerProductSpace

namespace CalderonN

variable {dim : ℕ} [NeZero dim] [Nontrivial (Fin dim)]

/-- The metric conormal flux with respect to unit Euclidean surface
measure on the fixed ball. -/
@[expose] def ballConormal (g : (MetricField dim)) (u : (X dim) → ℝ) (w : (X dim)) : ℝ :=
  ⟪w,metricFluxVector g u w⟫_ℝ

theorem continuousOn_ballConormal {U : Set (X dim)} (hU : IsOpen U) {g : (MetricField dim)}
    (hg : SmoothMetric U g) {u : (X dim) → ℝ} (hu : ContDiffOn ℝ ∞ u U) :
    ContinuousOn (ballConormal g u) U :=
  continuousOn_id.inner (contDiffOn_metricFluxVector hU hg hu).continuousOn

theorem unitSphereFlux_wronskian_eq_zero_of_harmonic
    {U : Set (X dim)} (hU : IsOpen U) (hB : closedBall (0 : (X dim)) 1 ⊆ U)
    {g : (MetricField dim)} (hg : SmoothMetric U g) {u v : (X dim) → ℝ}
    (hu : ContDiffOn ℝ ∞ u U) (hv : ContDiffOn ℝ ∞ v U)
    (hLapU : ∀ x ∈ ball (0 : (X dim)) 1, laplace g u x = 0)
    (hLapV : ∀ x ∈ ball (0 : (X dim)) 1, laplace g v x = 0) :
    unitSphereFlux (wronskianFlux g u v) = 0 := by
  obtain ⟨W,hW,hNear⟩ := exists_global_extension_on_closedUnitBall hU hB
    (contDiffOn_wronskianFlux hU hg hu hv)
  have hEq : unitSphereFlux W = unitSphereFlux (wronskianFlux g u v) := by
    unfold unitSphereFlux
    apply integral_congr_ae
    filter_upwards with w
    rw [(hNear w (sphere_subset_closedBall w.property)).eq_of_nhds]
  rw [← hEq,← integral_unitBall_coordinateFluxDivergence W hW]
  apply setIntegral_eq_zero_of_forall_eq_zero
  intro x hx
  rw [coordinateFluxDivergence_congr_germ (hNear x (ball_subset_closedBall hx))]
  change (∑ i, coordDeriv i (fun z => wronskianFlux g u v z i) x) = 0
  rw [divergence_wronskianFlux hU hg hu hv (hB (ball_subset_closedBall hx)),
    hLapU x hx,hLapV x hx]
  ring

private theorem ballConormal_eq_wronskian (g : (MetricField dim)) (u k : (X dim) → ℝ) (x : (X dim)) :
    ⟪x,wronskianFlux g u k x⟫_ℝ = k x * ballConormal g u x - u x * ballConormal g k x := by
  have he : wronskianFlux g u k x = k x • metricFluxVector g u x - u x • metricFluxVector g k x := by
    ext i
    simp only [wronskianFlux,metricFluxVector,PiLp.toLp_apply,PiLp.sub_apply,PiLp.smul_apply,smul_eq_mul]
  rw [he,inner_sub_right,real_inner_smul_right,real_inner_smul_right,ballConormal,ballConormal]

private theorem continuousOn_sphere_compact {f : (X dim) → ℝ} (hf : ContinuousOn f (sphere (0 : (X dim)) 1)) :
    Integrable (fun w : ↥(sphere (0 : (X dim)) 1) => f w) (chartSurfaceMeasure dim) := by
  letI : CompactSpace ↥(sphere (0 : (X dim)) 1) :=
    isCompact_iff_compactSpace.mp (isCompact_sphere (0 : (X dim)) 1)
  have hC := hf.comp_continuous continuous_subtype_val (fun w => w.property)
  exact hC.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

/-- Replacing the boundary kernel value by its harmonic extension
transposes the first conormal derivative onto that boundary value. -/
theorem unitSphereFlux_eq_conormal_density
    {U S : Set (X dim)} (hU : IsOpen U) (hS : IsOpen S)
    (hB : closedBall (0 : (X dim)) 1 ⊆ U) (hSphere : sphere (0 : (X dim)) 1 ⊆ S)
    {g : (MetricField dim)} (hg : SmoothMetric U g)
    {u v k : (X dim) → ℝ} (hu : ContDiffOn ℝ ∞ u U) (hv : ContDiffOn ℝ ∞ v U)
    (hk : ContDiffOn ℝ ∞ k S)
    (hLapU : ∀ x ∈ ball (0 : (X dim)) 1, laplace g u x = 0)
    (hLapV : ∀ x ∈ ball (0 : (X dim)) 1, laplace g v x = 0)
    (hEq : EqOn v k (sphere (0 : (X dim)) 1)) :
    unitSphereFlux (wronskianFlux g u k) =
      ∫ w : ↥(sphere (0 : (X dim)) 1), u w * (ballConormal g v w-ballConormal g k w) ∂(chartSurfaceMeasure dim) := by
  have hSU : sphere (0 : (X dim)) 1 ⊆ U := sphere_subset_closedBall.trans hB
  have hInt (f : (X dim) → ℝ) (hf : ContinuousOn f (sphere (0 : (X dim)) 1)) :
      Integrable (fun w : ↥(sphere (0 : (X dim)) 1) => f w) (chartSurfaceMeasure dim) :=
    continuousOn_sphere_compact hf
  have hS' : sphere (0 : (X dim)) 1 ⊆ U ∩ S := fun x hx => ⟨hSU hx,hSphere hx⟩
  have hkC := (continuousOn_ballConormal (hU.inter hS)
    ⟨fun i j => (hg.1 i j).mono inter_subset_left,fun x hx => hg.2 x hx.1⟩
    (hk.mono inter_subset_right)).mono hS'
  have hvC := (continuousOn_ballConormal hU hg hv).mono hSU
  have huC := (hu.continuousOn.mono hSU)
  let A : ↥(sphere (0 : (X dim)) 1) → ℝ := fun w => k w * ballConormal g u w
  let B : ↥(sphere (0 : (X dim)) 1) → ℝ := fun w => u w * ballConormal g v w
  let C : ↥(sphere (0 : (X dim)) 1) → ℝ := fun w => u w * ballConormal g k w
  have hA : Integrable A (chartSurfaceMeasure dim) :=
    hInt _ ((hk.continuousOn.mono hSphere).mul ((continuousOn_ballConormal hU hg hu).mono hSU))
  have hB' : Integrable B (chartSurfaceMeasure dim) := hInt _ (huC.mul hvC)
  have hC : Integrable C (chartSurfaceMeasure dim) := hInt _ (huC.mul hkC)
  have hV : (∫ w, A w-B w ∂(chartSurfaceMeasure dim)) = 0 := by
    rw [← unitSphereFlux_wronskian_eq_zero_of_harmonic hU hB hg hu hv hLapU hLapV]
    unfold unitSphereFlux
    apply integral_congr_ae
    filter_upwards with w
    simp only [A,B,ballConormal_eq_wronskian,hEq w.property]
  have hAB : (∫ w, A w ∂(chartSurfaceMeasure dim)) = ∫ w, B w ∂(chartSurfaceMeasure dim) := by
    rw [integral_sub hA hB'] at hV
    exact sub_eq_zero.mp hV
  calc
    _ = ∫ w, A w-C w ∂(chartSurfaceMeasure dim) := by
      unfold unitSphereFlux
      apply integral_congr_ae
      filter_upwards with w
      exact ballConormal_eq_wronskian g u k w
    _ = ∫ w, B w-C w ∂(chartSurfaceMeasure dim) := by rw [integral_sub hA hC,integral_sub hB' hC,hAB]
    _ = _ := by
      apply integral_congr_ae
      filter_upwards with w
      exact (mul_sub (u w) _ _).symm

end CalderonN
