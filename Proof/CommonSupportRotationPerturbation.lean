import Proof.RotatedBoundaryMultiplierDerivative
import Proof.CommonSupportOneBoundaryDerivative

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
open OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open OAI.AnisotropicCalderon.SphereHarmonic OAI.AnisotropicCalderon.SmoothSphereRotation

/-- A constant flat term contributes no angle derivative. The compact
perturbation's actual generator is the rotation of the true local remainder. -/
theorem commonSupport_rotation_perturbation_generators
    (a : ℝ × X → Mat) (ha : ContDiff ℝ ∞ a) (S : Set X) (hS : IsCompact S)
    (hz : ∀ θ z,z ∉ S → a (θ,z) = 0) (R : X → Mat) (C : Mat) (i j : I)
    (hR : ∀ z ∈ Metric.closedBall (0:X) 2,HasDerivAt
      (fun θ : ℝ => coordinateRotationPrincipalFamily i j (fun v : ℝ × X => R v.2) ((θ,0),z))
      (rotationPrincipalCoefficientDerivative i j R z) 0)
    (hRep : ∀ z ∈ Metric.closedBall (0:X) 2,a =ᶠ[𝓝 ((0:ℝ),z)]
      (fun p : ℝ × X => C+coordinateRotationPrincipalFamily i j (fun v : ℝ × X => R v.2) ((p.1,0),p.2)))
    (q : ℝ) (hq : 0 ≤ q)
    (h0 : ∀ z ∈ (ballOpens:Set X),‖rotationPrincipalCoefficientDerivative i j R z‖ ≤ q)
    (h1 : ∀ z ∈ (ballOpens:Set X),‖fderiv ℝ (rotationPrincipalCoefficientDerivative i j R) z‖ ≤ q) :
    ∃ b : X → Mat,ContDiff ℝ ∞ b ∧ (∀ z,z ∉ S → b z = 0) ∧
      (∀ z,HasDerivAt (fun θ => a (θ,z)) (b z) 0) ∧
      (∀ z ∈ (ballOpens:Set X),‖b z‖ ≤ q) ∧
      ∀ z ∈ (ballOpens:Set X),‖fderiv ℝ b z‖ ≤ q := by
  obtain ⟨b,hb,hzb,hAngle⟩ := exists_commonSupport_angle_generator a ha S hz
  have hGerm (z : X) (hzB : z ∈ (ballOpens:Set X)) :
      b =ᶠ[𝓝 z] rotationPrincipalCoefficientDerivative i j R := by
    have hzTwo : z ∈ Metric.ball (0:X) 2 := Metric.ball_subset_ball (by norm_num) hzB
    filter_upwards [Metric.isOpen_ball.mem_nhds hzTwo] with w hw
    have hwC := Metric.ball_subset_closedBall hw
    have hNear := (hRep w hwC).comp_tendsto
      (show Tendsto (fun θ : ℝ => (θ,w)) (𝓝 0) (𝓝 (0,w)) from
        (continuousAt_id.prodMk continuousAt_const).tendsto)
    have hCurve := (hasDerivAt_const (0:ℝ) C).add
      (hR w hwC)
    simp only [zero_add] at hCurve
    exact (hAngle w).unique (hCurve.congr_of_eventuallyEq hNear)
  exact ⟨b,hb,hzb,hAngle,
    (fun z hzB => by rw [(hGerm z hzB).eq_of_nhds];exact h0 z hzB),
    (fun z hzB => by rw [(hGerm z hzB).fderiv_eq];exact h1 z hzB)⟩

end ShrinkingSpheres
