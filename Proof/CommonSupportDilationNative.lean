import Proof.RelativeDilationGenerator
import Proof.CommonSupportDirectionalGenerators

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter
open scoped ContDiff Topology Matrix.Norms.Elementwise
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.EnergyBridge OAI.AnisotropicCalderon.DirichletFamily

def relativeDilationFamily (f : X → Mat) (p : ℝ × X) : Mat := f ((1+p.1) • p.2)

/-- A genuine compact representative of the dilation family inherits native
    parameter derivative bounds from the same spatial C1/C2 data. -/
theorem commonSupport_dilation_generator_bounds
    (A : ℝ × X → Mat) (hA : ContDiff ℝ ∞ A) (S : Set X) (hS : IsCompact S)
    (hz : ∀ t z,z ∉ S → A (t,z) = 0) (f : X → Mat) (C : Mat)
    (hRep : ∀ z ∈ Metric.closedBall (0:X) 2,A =ᶠ[𝓝 (0,z)] (fun p => C+relativeDilationFamily f p))
    (hf : ∀ z ∈ Metric.closedBall (0:X) 2,ContDiffAt ℝ ∞ f z)
    (q1 q2 : ℝ) (hq1 : 0 ≤ q1) (hq2 : 0 ≤ q2)
    (hD : ∀ z ∈ (ballOpens:Set X),‖fderiv ℝ f z‖ ≤ q1)
    (hD2 : ∀ z ∈ (ballOpens:Set X),‖fderiv ℝ (fderiv ℝ f) z‖ ≤ q2) :
    ∃ b : X → Mat,ContDiff ℝ ∞ b ∧ (∀ z,z ∉ S → b z = 0) ∧
      (∀ z,HasDerivAt (fun t => A (t,z)) (b z) 0) ∧
      (∀ z ∈ (ballOpens:Set X),‖b z‖ ≤ q1+q2) ∧
      ∀ z ∈ (ballOpens:Set X),‖fderiv ℝ b z‖ ≤ q1+q2 := by
  obtain ⟨b,hb,hzb,hCurve⟩ := exists_commonSupport_angle_generator A hA S hz
  have hBEq (z : X) (hzB : z ∈ Metric.closedBall (0:X) 2) : b z = relativeDilationGenerator f z := by
    have hInput : Tendsto (fun t : ℝ => (t,z)) (𝓝 0) (𝓝 (0,z)) :=
      continuousAt_id.prodMk continuousAt_const
    have hNear : (fun t : ℝ => A (t,z)) =ᶠ[𝓝 0] (fun t => C+f ((1+t) • z)) :=
      (hRep z hzB).comp_tendsto hInput
    have hRaw := hasDerivAt_relative_dilation f z ((hf z hzB).differentiableAt (by simp))
    have hRawC : HasDerivAt (fun t : ℝ => C+f ((1+t) • z)) (relativeDilationGenerator f z) 0 := by
      have hSum := (hasDerivAt_const (0:ℝ) C).add hRaw
      change HasDerivAt (fun t : ℝ => C+f ((1+t) • z)) _ 0 at hSum
      simpa only [zero_add] using hSum
    exact (hCurve z).unique (hRawC.congr_of_eventuallyEq hNear)
  have hValue (z : X) (hzB : z ∈ (ballOpens:Set X)) : ‖b z‖ ≤ q1+q2 := by
    have hNz : ‖z‖ ≤ 1 := by
      have hDist : dist z 0 < 1 := hzB
      simpa only [dist_zero_right] using hDist.le
    rw [hBEq z (unitBall_subset_closedBall_two hzB)]
    exact (norm_relativeDilationGenerator_le f z q1 (hD z hzB)).trans
      ((mul_le_mul_of_nonneg_left hNz hq1).trans (by linarith))
  have hSpatial (z : X) (hzB : z ∈ (ballOpens:Set X)) : ‖fderiv ℝ b z‖ ≤ q1+q2 := by
    have hNz : ‖z‖ ≤ 1 := by
      have hDist : dist z 0 < 1 := hzB
      simpa only [dist_zero_right] using hDist.le
    have hz2 : z ∈ Metric.ball (0:X) 2 := by
      simpa only [Metric.mem_ball,dist_zero_right] using (lt_of_le_of_lt hNz (by norm_num : (1:ℝ) < 2))
    have hNear : b =ᶠ[𝓝 z] relativeDilationGenerator f := by
      filter_upwards [Metric.isOpen_ball.mem_nhds hz2] with w hw
      exact hBEq w (Metric.ball_subset_closedBall hw)
    rw [hNear.fderiv_eq]
    exact (norm_fderiv_relativeDilationGenerator_le f z (hf z (unitBall_subset_closedBall_two hzB))
      q1 q2 hq1 hq2 (hD z hzB) (hD2 z hzB)).trans
        (by nlinarith only [mul_le_mul_of_nonneg_left hNz hq2])
  exact ⟨b,hb,hzb,hCurve,hValue,hSpatial⟩

/-- A genuine compact representative of the dilation family inherits native
    parameter derivative bounds from the same spatial C1/C2 data. -/
theorem commonSupport_dilation_native_bounds
    (A : ℝ × X → Mat) (hA : ContDiff ℝ ∞ A) (S : Set X) (hS : IsCompact S)
    (hz : ∀ t z,z ∉ S → A (t,z) = 0) (f : X → Mat) (C : Mat)
    (hRep : ∀ z ∈ Metric.closedBall (0:X) 2,A =ᶠ[𝓝 (0,z)] (fun p => C+relativeDilationFamily f p))
    (hf : ∀ z ∈ Metric.closedBall (0:X) 2,ContDiffAt ℝ ∞ f z)
    (q1 q2 : ℝ) (hq1 : 0 ≤ q1) (hq2 : 0 ≤ q2)
    (hD : ∀ z ∈ (ballOpens:Set X),‖fderiv ℝ f z‖ ≤ q1)
    (hD2 : ∀ z ∈ (ballOpens:Set X),‖fderiv ℝ (fderiv ℝ f) z‖ ≤ q2) :
    CommonSupportNativeDerivativeBounds A hA S hS hz (q1+q2) := by
  obtain ⟨b,hb,hzb,hCurve,hValue,hSpatial⟩ := commonSupport_dilation_generator_bounds
    A hA S hS hz f C hRep hf q1 q2 hq1 hq2 hD hD2
  exact commonSupport_native_derivatives_of_generator_bounds A hA S hS hz b hb hzb hCurve
    (q1+q2) (add_nonneg hq1 hq2) hValue hSpatial

end ShrinkingSpheres
