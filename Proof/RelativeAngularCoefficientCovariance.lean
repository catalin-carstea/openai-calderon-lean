import Proof.NormalizedRelativeAngularCurve
import Proof.NormalFrameRotationCoefficient

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2800000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set
open scoped ContDiff Topology Matrix.Norms.Elementwise
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.SmoothSphereRotation
open OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

/-- Rotating the normalized frame gives the genuine orthogonal coefficient
    covariance at EVERY positive independent parameter. No equivariance of
    the Gram--Schmidt extension away from orthonormal frames is asserted. -/
theorem Elliptic.normalFrameRelativeCoefficient_angular_curve {Ω : Set X} {K : ℝ} {g : MetricField}
    (h : Elliptic Ω K g) (hK : 0 < K) (g₁ : MetricField) (E : X × X → X) (r : ℝ)
    (p : NormalFrameRelativeParameter) (hp : p ∈ normalFrameRelativePositiveDomain Ω)
    (i j : I) (θ : ℝ) (z : X) :
    normalFrameRelativeCoefficient g g₁ E r (normalFrameRelativeAngularCurve g p i j θ,z) =
      coordinateRotationPrincipalFamily i j
        (fun q : ℝ × X => normalFrameRelativeCoefficient g g₁ E r (p,q.2)) ((θ,0),z) := by
  let L := (normalFrameRelativeNormalization g p).1.2
  let R := (coordinateRotationIsometry i j θ).toContinuousLinearEquiv.toContinuousLinearMap
  have he := h.normalFrameRelativeAngularCurve_orthonormal hK p hp i j θ
  have hFix : normalFrameRelativeNormalization g (normalFrameRelativeAngularCurve g p i j θ) =
      normalFrameRelativeAngularCurve g p i j θ :=
    normalFrameRelativeNormalization_eq_self g _ he
  calc
    _ = normalFrameNormalizedCoefficient g g₁ E ((p.1.1,((1+p.2)*r,L.comp R)),z) := by
      rw [normalFrameRelativeCoefficient_eq_raw_normalized,hFix]
      rfl
    _ = (coordinateRotationMatrix i j θ).transpose*
        normalFrameNormalizedCoefficient g g₁ E ((p.1.1,((1+p.2)*r,L)),coordinateRotation i j θ z)*
          coordinateRotationMatrix i j θ :=
      normalFrameNormalizedCoefficient_coordinate_rotation g g₁ E p.1.1 ((1+p.2)*r) L i j θ z
    _ = _ := by
      change (coordinateRotationMatrix i j θ).transpose*_*coordinateRotationMatrix i j θ =
        (coordinateRotationMatrix i j θ).transpose*
          normalFrameRelativeCoefficient g g₁ E r (p,coordinateRotation i j θ z)*coordinateRotationMatrix i j θ
      rw [normalFrameRelativeCoefficient_eq_raw_normalized]
      rfl

theorem Elliptic.normalFrameRelativeFirstCovector_angular_curve {Ω : Set X} {K : ℝ} {g : MetricField}
    (h : Elliptic Ω K g) (hK : 0 < K) (g₁ : MetricField)
    (p : NormalFrameRelativeParameter) (hp : p ∈ normalFrameRelativePositiveDomain Ω)
    (i j : I) (θ : ℝ) :
    normalFrameRelativeFirstCovector g g₁ (normalFrameRelativeAngularCurve g p i j θ) =
      (normalFrameRelativeFirstCovector g g₁ p).comp
        (coordinateRotationIsometry i j θ).toContinuousLinearEquiv.toContinuousLinearMap := by
  have he := h.normalFrameRelativeAngularCurve_orthonormal hK p hp i j θ
  have hFix := normalizedOrthonormalFrameParameter_eq_self g
    (normalFrameRelativeZeroL (normalFrameRelativeAngularCurve g p i j θ)) he
  change normalizedOrthonormalFrameParameter g
      ((normalFrameRelativeAngularCurve g p i j θ).1.1,(0,(normalFrameRelativeAngularCurve g p i j θ).1.2)) =
    ((normalFrameRelativeAngularCurve g p i j θ).1.1,(0,(normalFrameRelativeAngularCurve g p i j θ).1.2)) at hFix
  unfold normalFrameRelativeFirstCovector
  rw [hFix]
  apply ContinuousLinearMap.ext
  intro z
  rfl

end ShrinkingSpheres
