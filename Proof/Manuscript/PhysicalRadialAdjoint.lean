module

public import Proof.CalderonN.ActualMovingTraceAdjoint
public import Proof.CalderonN.GaussRadialTraceAdjoint

import Proof.CalderonN.GreenWeak
import Mathlib.Tactic

public section

noncomputable section

open Set Metric CalderonN
open scoped ContDiff InnerProductSpace

namespace CalderonPaper

open OAI.AnisotropicCalderon.SmoothSphereRotation

variable {dim : ℕ} [NeZero dim] [Nontrivial (Fin dim)]

/-- The Gauss radial Poisson response minus the exact rotation term, in
normalized Euclidean angular coordinates. -/
@[expose] def radialBallVelocityAdjoint (M : MetricField dim) (V : X dim → X dim)
    (W : X dim → ℝ) (φ : X dim → ℂ) (z : X dim) : ℂ :=
  let bR := fixedBallPoisson M (fun x => (φ x).re * ⟪x,V x⟫_ℝ / W x)
  let bI := fixedBallPoisson M (fun x => (φ x).im * ⟪x,V x⟫_ℝ / W x)
  ⟨W z * fderiv ℝ bR z z -
      ∑ j, ∑ k, sphereRotationDerivative j k (fun x => (φ x).re * (x j * V x k)) z,
    W z * fderiv ℝ bI z z -
      ∑ j, ∑ k, sphereRotationDerivative j k (fun x => (φ x).im * (x j * V x k)) z⟩

omit [NeZero dim] [Nontrivial (Fin dim)] in
/-- A classical fixed-ball solution is shared by metrics agreeing on the
closed ball. Harmonicity only uses the open ball. -/
theorem FixedBallSolution.congr_metric_on_closedBall
    {g M : MetricField dim} {d b : X dim → ℝ}
    (h : FixedBallSolution M d b) (hEq : EqOn g M (closedBall (0 : X dim) 1)) :
    FixedBallSolution g d b := by
  refine ⟨h.1,h.2.1,fun z hz => ?_⟩
  rw [laplace_congrOn isOpen_ball (hEq.mono ball_subset_closedBall) (fun _ _ => rfl) hz]
  exact h.2.2 z hz

set_option maxHeartbeats 3000000 in
/-- The literal physical adjoint is the normalized Gauss response divided
by the radius. The Poisson problem may use a smooth metric representative
agreeing with the moving-ball metric on the closed ball. -/
theorem actualMovingTraceAdjoint_eq_radialBallVelocityAdjoint
    {γ g : MetricField dim} {E : X dim × X dim → X dim} {e : Frame dim}
    {r : X dim → ℝ} (i : I dim) (y : X dim)
    (hFrame : ∀ j k, metricPair γ y (e y j) (e y k) = if j=k then 1 else 0)
    {U S U' : Set (X dim)} (hU : IsOpen U) (hS : IsOpen S) (hU' : IsOpen U')
    (hBU : closedBall (0 : X dim) 1 ⊆ U) (hBU' : closedBall (0 : X dim) 1 ⊆ U')
    (hSS : standardSphere dim ⊆ S) (hSU : S ⊆ U) (hS₀ : (0 : X dim) ∉ S)
    (hg : SmoothMetric U (normalizedBallMetric g E e y (r y)))
    (hV : ContDiffOn ℝ ∞ (fun z => scaledNormalTraceVelocity γ E e y (r y)
      (coordDeriv i r y) z (axis i)) S)
    {W : X dim → ℝ} (hW : ContDiffOn ℝ ∞ W S) (hW₀ : ∀ z ∈ S, W z ≠ 0)
    {c : ℝ} (hc : c ≠ 0)
    (hRadial : EqOn (ballConormalVector (normalizedBallMetric g E e y (r y)))
      (fun z => (c * W z) • z) (standardSphere dim))
    {M : MetricField dim} (hM : SmoothMetric U' M)
    (hEq : EqOn (normalizedBallMetric g E e y (r y)) M (closedBall (0 : X dim) 1))
    {φ : X dim → ℂ} (hφ : ContDiffOn ℝ ∞ φ S)
    {z : X dim} (hz : z ∈ standardSphere dim) :
    actualMovingTraceAdjoint γ g E e r i y
      (fun v => φ (movingBallToFrame γ e (y,v)).2) (frameVector e y z) =
    ((r y)⁻¹ : ℝ) • radialBallVelocityAdjoint M
      (fun x => scaledNormalTraceVelocity γ E e y (r y) (coordDeriv i r y) x (axis i)) W φ z := by
  let v (x : X dim) := scaledNormalTraceVelocity γ E e y (r y) (coordDeriv i r y) x (axis i)
  let m := normalizedBallMetric g E e y (r y)
  have hInner : ContDiffOn ℝ ∞ (fun x => ⟪x,v x⟫_ℝ) S := contDiffOn_id.inner ℝ hV
  have hR : ContDiffOn ℝ ∞ (fun x => (φ x).re) S := Complex.reCLM.contDiff.comp_contDiffOn hφ
  have hI : ContDiffOn ℝ ∞ (fun x => (φ x).im) S := Complex.imCLM.contDiff.comp_contDiffOn hφ
  have hResponse {f : X dim → ℝ} (hf : ContDiffOn ℝ ∞ f S) :
      FixedBallSolution m (fun x => f x * ⟪x,v x⟫_ℝ / W x)
        (fixedBallPoisson M (fun x => f x * ⟪x,v x⟫_ℝ / W x)) := by
    have hDatum : smoothNear (fun x => f x * ⟪x,v x⟫_ℝ / W x) (standardSphere dim) :=
      ⟨S,hS,hSS,(hf.mul hInner).div hW hW₀⟩
    exact FixedBallSolution.congr_metric_on_closedBall
      (fixedBallPoisson_solution hU' hBU' hM hDatum) hEq
  have hPair (x : X dim) : movingBallToFrame γ e (y,frameVector e y x) = (y,x) :=
    movingBallToFrame_fromFrame hFrame
  have heR : (fun q : X dim × X dim => (φ (movingBallToFrame γ e (y,frameVector e y q.2)).2).re) =
      (fun q => (φ q.2).re) := by funext q; rw [hPair]
  have heI : (fun q : X dim × X dim => (φ (movingBallToFrame γ e (y,frameVector e y q.2)).2).im) =
      (fun q => (φ q.2).im) := by funext q; rw [hPair]
  have hGaussR := parametricBallVelocityAdjoint_gauss_radial_response y hU hS hBU hSS hSU hS₀
    (g := movingBallMetric g E e r) (V := movingBallScaledVelocity γ E e r i)
    (ψ := fun q => (φ q.2).re) hg hV hR c hc W hRadial (hResponse hR) hz
  have hGaussI := parametricBallVelocityAdjoint_gauss_radial_response y hU hS hBU hSS hSU hS₀
    (g := movingBallMetric g E e r) (V := movingBallScaledVelocity γ E e r i)
    (ψ := fun q => (φ q.2).im) hg hV hI c hc W hRadial (hResponse hI) hz
  dsimp only [actualMovingTraceAdjoint]
  rw [hPair,heR,heI,hGaussR,hGaussI]
  rw [Complex.real_smul]
  apply Complex.ext <;> simp [radialBallVelocityAdjoint, Complex.mul_re, Complex.mul_im,
    movingBallScaledVelocity, v]

end CalderonPaper
