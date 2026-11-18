import Proof.CoframeScalarRotationCalculus
import Proof.RelativeCoframeSobolevRegularity
import Proof.RelativeAngularDerivativeCurve
import Proof.RelativeCoframeAngularCurve
import Proof.ScalarLinearCombinationDerivative
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2800000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter
open scoped ContDiff Topology
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.DirichletFamily
open OAI.AnisotropicCalderon.SphereHarmonic
open OAI.AnisotropicCalderon.SmoothSphereRotation

lemma Elliptic.relativeCoframeNormal_angularDerivative {Ω : Set X} (hΩ : IsOpen Ω)
    {K : ℝ} {g : MetricField} (h : Elliptic Ω K g) (hK : 0 < K) (s : ℝ) (a : X)
    (p : NormalFrameRelativeParameter) (hp : p ∈ normalFrameRelativePositiveDomain Ω) (i j : I) :
    normalFrameRelativeAngularDerivative g (relativeCoframeNormalSobolevL s g a) i j p =
      relativeCoframeAngularSobolevL s g a i j p := by
  have hSmooth : ContDiffAt ℝ ∞ (relativeCoframeNormalSobolevL s g a)
      (normalFrameRelativeNormalization g p) := (h.contDiffOn_relativeCoframeSobolevMultiplier hΩ hK s a).contDiffAt
    ((isOpen_normalFrameRelativePositiveDomain hΩ).mem_nhds (h.normalFrameRelativeNormalization_mem hK p hp))
  have hNative := hasDerivAt_relativeAngularFamily g (relativeCoframeNormalSobolevL s g a) p i j
    (hSmooth.differentiableAt (by simp))
  have hSum := hasDerivAt_scalar_linearCombination
    (fun k θ => normalFrameRelativeCoframeValue g a k (normalFrameRelativeAngularCurve g p i j θ))
    (fun k => (if k=i then normalFrameRelativeCoframeValue g a j p else 0)-
      (if k=j then normalFrameRelativeCoframeValue g a i p else 0))
    (coordinateMultiplierSobolevL s) 0 (fun k => h.hasDerivAt_relativeCoframeValue_angular hK a k p hp i j)
  have hh := hNative.unique hSum
  have hRot := @sum_rotation_coordinates (SphereSobolev s →L[ℝ] SphereSobolev s)
    (inferInstance : NormedAddCommGroup (SphereSobolev s →L[ℝ] SphereSobolev s)).toAddCommGroup
    (inferInstance : NormedSpace ℝ (SphereSobolev s →L[ℝ] SphereSobolev s)).toModule
    (fun k => normalFrameRelativeCoframeValue g a k p) (coordinateMultiplierSobolevL s) i j
  exact hh.trans hRot
end ShrinkingSpheres
