import Proof.BoundaryMatrixAngleDerivative
import Proof.CoordinateRotationGenerator

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter
open scoped ContDiff Topology Matrix.Norms.Elementwise
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.EnergyBridge OAI.AnisotropicCalderon.DirichletFamily
open OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open OAI.AnisotropicCalderon.SphereHarmonic
open OAI.AnisotropicCalderon.NativeBoundaryCoefficientFamilies
open OAI.AnisotropicCalderon.SmoothSphereRotation

/-- Full-angle agreement on the enlarged ball identifies the actual compact
    generator as a germ along every point of the physical ball. -/
theorem commonSupport_rotated_angle_generator_germ
    (a : ℝ × X → Mat) (R b : X → Mat) (i j : I)
    (hAngle : ∀ z,HasDerivAt (fun θ => a (θ,z)) (b z) 0)
    (hR : ∀ z ∈ Metric.closedBall (0:X) 2,DifferentiableAt ℝ R z)
    (hRep : ∀ θ z,z ∈ Metric.closedBall (0:X) 2 → a (θ,z) = coordinateRotationPrincipalFamily i j
      (fun v : ℝ × X => R v.2) ((θ,0),z)) (z : X) (hz : z ∈ (ballOpens:Set X)) :
    b =ᶠ[𝓝 z] rotationPrincipalCoefficientDerivative i j R := by
  have hBall : z ∈ Metric.ball (0:X) 1 := hz
  have hzTwo : z ∈ Metric.ball (0:X) 2 := Metric.ball_subset_ball (by norm_num) hBall
  filter_upwards [Metric.isOpen_ball.mem_nhds hzTwo] with w hw
  have hwC := Metric.ball_subset_closedBall hw
  have hFun : (fun θ => a (θ,w)) = fun θ => coordinateRotationPrincipalFamily i j
      (fun v : ℝ × X => R v.2) ((θ,0),w) := funext (fun θ => hRep θ w hwC)
  have hA := hAngle w
  rw [hFun] at hA
  exact hA.unique (hasDerivAt_coordinateRotationPrincipal_zero i j R w (hR w hwC))

/-- Genuine normal/tangent multiplier derivatives of any actual rotated
    representative depend only on the local rotation-generator C1 bounds. -/
theorem norm_fderiv_rotated_commonSupport_boundary_matrix_le
    (a : ℝ × X → Mat) (ha : ContDiff ℝ ∞ a) (S : Set X) (hS : IsCompact S)
    (hz : ∀ θ z,z ∉ S → a (θ,z) = 0) (R : X → Mat) (i j : I)
    (hR : ∀ z ∈ Metric.closedBall (0:X) 2,DifferentiableAt ℝ R z)
    (hRep : ∀ θ z,z ∈ Metric.closedBall (0:X) 2 → a (θ,z) = coordinateRotationPrincipalFamily i j
      (fun v : ℝ × X => R v.2) ((θ,0),z))
    (q : ℝ) (hq : 0 ≤ q)
    (h0 : ∀ z ∈ (ballOpens:Set X),‖rotationPrincipalCoefficientDerivative i j R z‖ ≤ q)
    (h1 : ∀ z ∈ (ballOpens:Set X),‖fderiv ℝ (rotationPrincipalCoefficientDerivative i j R) z‖ ≤ q) :
    ‖fderiv ℝ (fun θ => negativeBoundaryCoefficientMulL (normalCoefficientJetsFamily a ha S hS hz θ)) 0‖ ≤
        boundaryHalfDerivativeBudget*(36*q) ∧
      ∀ k : I,‖fderiv ℝ (fun θ => negativeBoundaryCoefficientMulL (tangentCoefficientJetsFamily a ha S hS hz k θ)) 0‖ ≤
        boundaryHalfDerivativeBudget*(78*q) := by
  have hGeneratorTheorem := exists_commonSupport_angle_generator a ha S hz
  obtain ⟨b,hb,hzb,hAngle⟩ := hGeneratorTheorem
  have hGerm (z : X) (hzB : z ∈ (ballOpens:Set X)) :=
    commonSupport_rotated_angle_generator_germ a R b i j hAngle hR hRep z hzB
  exact norm_fderiv_commonSupport_boundary_matrix_angle_le a ha S hS hz b hb hzb hAngle q hq
    (fun z hzB => by rw [(hGerm z hzB).eq_of_nhds];exact h0 z hzB)
    (fun z hzB => by rw [(hGerm z hzB).fderiv_eq];exact h1 z hzB)

end ShrinkingSpheres
