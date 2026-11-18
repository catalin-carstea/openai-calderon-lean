import Proof.NativeRelativeRadialRotationCovariance
import Proof.BoundaryAdjointOrthogonalCovariance
import Proof.NativeRelativeFullAdjointJets

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 2000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter MeasureTheory
open scoped ContDiff Topology ENNReal InnerProductSpace Matrix.Norms.Elementwise
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.EnergyBridge OAI.AnisotropicCalderon.DirichletFamily
open OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open OAI.AnisotropicCalderon.SphereHarmonic OAI.AnisotropicCalderon.SmoothSphereRotation
attribute [local irreducible] sphereSobolevDegreeL
attribute [local instance] TauCeti.W1p0.instNormedAddCommGroup TauCeti.W1p0.instInnerProductSpace

/-- Native true radial adjunction transports the same response covariance
    to its actual adjoint at every parameter of the common domain. -/
theorem native_relative_radial_adjoint_rotation_covariance
    {Y Ω : Set X} {d : Data} {y : X} {N : ℕ} {Z C : ℝ}
    {q : NormalFrameRelativeCoefficientJetFamily Y Ω d.γ d.g₁ d.expMap y
      (frameVectorLinear d.frame y) (d.radius y) N Z C}
    (t : NormalFrameRelativeResponsePacket q) (V : t.SymmetricAdjointDomain)
    {K : ℝ} (h : Elliptic Ω K d.γ) (hK : 0 < K) (hZ : 2 ≤ Z)
    (p : NormalFrameRelativeParameter) (hp : p ∈ V.domain)
    (i j : I) (θ : ℝ) (hθ : normalFrameRelativeAngularCurve d.γ p i j θ ∈ V.domain) :
    (t.fullAdjoint
      (normalFrameRelativeAngularCurve d.γ p i j θ)).comp
        (sphereSobolevOrthogonalPullbackL 1 (coordinateRotationIsometry i j θ)) =
      (sphereSobolevOrthogonalPullbackL 0 (coordinateRotationIsometry i j θ)).comp
        (t.fullAdjoint p) := by
  let pθ := normalFrameRelativeAngularCurve d.γ p i j θ
  let e := coordinateRotationIsometry i j θ
  let P0 := sphereSobolevOrthogonalPullbackL 0 e
  let P1 := sphereSobolevOrthogonalPullbackL 1 e
  have hAdjθ := V.fullPair pθ hθ
  have hAdj0 := V.fullPair p hp
  have hRCov := native_relative_radial_rotation_covariance t V h hK hZ p hp i j θ hθ
  have hDCov (u : SphereSobolev 1) : (t.response pθ+sphereSobolevDegreeL) (P1 u) = P0 ((t.response p+sphereSobolevDegreeL) u) := by
    have hRValue := congrArg (fun T : SphereSobolev 1 →L[ℝ] SphereSobolev 0 => T u) hRCov
    have hDegree := congrArg (fun T : SphereSobolev 1 →L[ℝ] SphereSobolev 0 => T u) (sphereSobolevDegreeL_orthogonal_covariance e)
    exact (congrArg₂ (fun x y : SphereSobolev 0 => x+y) hRValue hDegree).trans (P0.map_add _ _).symm
  exact boundary_adjoint_orthogonal_covariance e _ _ _ _ hAdj0 hAdjθ hDCov


end ShrinkingSpheres
