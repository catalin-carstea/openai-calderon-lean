import Proof.OrthogonalEllipticity
import Proof.Archive.CoordinateRotationCoefficientFamily
import Proof.UniformStrongC1Neighborhood

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set
open scoped Matrix.Norms.Elementwise
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.EnergyBridge OAI.AnisotropicCalderon.DirichletFamily
open OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

/-- Any native coefficient witness for a rotated actual elliptic coefficient
    has its genuine strong Dirichlet inverse. This applies to affine-assembled
    families just as it does to direct rotated common-support representatives. -/
theorem strongDirichletOperator_invertible_of_rotated_coefficient
    (H : MetricField) (KP : ℝ) (hKP : 1 ≤ KP)
    (hEll : Elliptic (Metric.closedBall (0:X) 2) KP H)
    (i j : I) (θ : ℝ) (F : SmoothCoefficientMatrix 2)
    (hField : ∀ z ∈ (ballOpens:Set X),coefficientMatrixField 2 F z =
      coordinateRotationPrincipalFamily i j (fun v : ℝ × X => principalCoefficient H v.2) ((θ,0),z)) :
    (strongDirichletOperator fixedSobolevCalculus 0 F).IsInvertible := by
  have hUE := (hEll.principalCoefficient_tau hKP).mono_set unitBall_subset_closedBall_two
  have hRot := uniformlyEllipticOn_unitBall_orthogonal
    (OAI.AnisotropicCalderon.SmoothSphereRotation.coordinateRotationIsometry i j θ)
    (principalCoefficient H) _ _ hUE
  apply strongDirichletOperator_isInvertible_of_elliptic fixedSobolevCalculus fixedDirichletRegularity 0 F
  apply hRot.congr
  intro z hz
  exact (hField z hz).trans (coordinateRotationPrincipalFamily_eq_orthogonal i j
    (fun v : ℝ × X => principalCoefficient H v.2) θ 0 z)

end ShrinkingSpheres
