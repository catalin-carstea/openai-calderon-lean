import Proof.NativeTaylorAngularPacket
import Proof.NativeHalfTaylorHigherEndpoints
import Proof.NativeAdjointHalfTaylor
import Proof.EndpointCompatibleDerivative
import Proof.BalancedRotationCommutator
import Proof.BalancedDegreeCommutator
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3200000
set_option maxSynthPendingDepth 30
set_option maxRecDepth 2400
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
open Set Filter
open scoped ContDiff Topology InnerProductSpace
namespace ShrinkingSpheres.NormalFrameRelativeResponsePacket
open OAI.AnisotropicCalderon.DirichletFamily OAI.AnisotropicCalderon.SphereHarmonic
variable {Y Ω : Set X} {d : Data} {y : X} {N : ℕ} {Z CQ : ℝ}
  {q : NormalFrameRelativeCoefficientJetFamily Y Ω d.γ d.g₁ d.expMap y
    (frameVectorLinear d.frame y) (d.radius y) N Z CQ}

lemma adjointTaylor_rotation_low_endpoint (t : NormalFrameRelativeResponsePacket q)
    (V : t.SymmetricAdjointDomain) (hZ : 2 ≤ Z) (F0 : SmoothCoefficientMatrix 2)
    (hF0 : ∀ z ∈ Metric.closedBall (0:X) 2,coefficientMatrixField 2 F0 z=1)
    (p : NormalFrameRelativeParameter) (hp : p ∈ V.domain)
    (he : ∀ i j,metricPair d.γ p.1.1 (p.1.2 (axis i)) (p.1.2 (axis j))=if i=j then 1 else 0)
    (i j : I) :
    (sphereSobolevInclusionL 0 (-(1/2:ℝ)) (by norm_num)).comp
      (normalFrameRelativeAngularDerivative d.γ t.adjointTaylor i j p)=
      (fderiv ℝ t.adjointHalfTaylor p (normalFrameRelativeAngularTangent d.γ p i j)).comp
        (sphereSobolevInclusionL 1 (1/2:ℝ) (by norm_num)) := by
  have hA := (t.contDiffOn_adjointTaylor.contDiffAt (t.domainOpen.mem_nhds (V.sub hp))).differentiableAt (by simp)
  have hL := (V.contDiffOn_adjointHalfTaylor.contDiffAt (V.domainOpen.mem_nhds hp)).differentiableAt (by simp)
  have hCompat : ∀ᶠ x in 𝓝 p,
      (sphereSobolevInclusionL 0 (-(1/2:ℝ)) (by norm_num)).comp (t.adjointTaylor x)=
        (t.adjointHalfTaylor x).comp (sphereSobolevInclusionL 1 (1/2:ℝ) (by norm_num)) := by
    filter_upwards [V.domainOpen.mem_nhds hp] with x hx
    exact V.adjointHalfTaylor_coarse_compatible hZ F0 hF0 x hx
  have hD := compatible_endpoint_fderiv t.adjointTaylor t.adjointHalfTaylor _ _ p
    (normalFrameRelativeAngularTangent d.γ p i j) hA hL hCompat
  simpa only [normalFrameRelativeAngularDerivative,normalFrameRelativeNormalization_eq_self d.γ p he] using hD

lemma adjointTaylor_balanced_rotation_commutator (t : NormalFrameRelativeResponsePacket q)
    (V : t.SymmetricAdjointDomain) {K : ℝ} (h : Elliptic Ω K d.γ) (hK : 0 < K) (hZ : 2 ≤ Z)
    (F0 : SmoothCoefficientMatrix 2)
    (hF0 : ∀ z ∈ Metric.closedBall (0:X) 2,coefficientMatrixField 2 F0 z=1)
    (p : NormalFrameRelativeParameter) (hp : p ∈ V.domain)
    (he : ∀ i j,metricPair d.γ p.1.1 (p.1.2 (axis i)) (p.1.2 (axis j))=if i=j then 1 else 0)
    (i j : I) :
    (sphereSobolevRotationL (1/2:ℝ) i j).comp (V.adjointHigherTaylor h hK hZ p)-
      (t.adjointHalfTaylor p).comp (sphereSobolevRotationL (3/2:ℝ) i j)=
        (fderiv ℝ t.adjointHalfTaylor p (normalFrameRelativeAngularTangent d.γ p i j)).comp
          (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)) := by
  exact balanced_rotation_commutator i j (t.adjointTaylor p)
    (normalFrameRelativeAngularDerivative d.γ t.adjointTaylor i j p) (t.adjointHalfTaylor p)
    (fderiv ℝ t.adjointHalfTaylor p (normalFrameRelativeAngularTangent d.γ p i j))
    (V.adjointHigherTaylor h hK hZ p)
    (V.adjointHalfTaylor_coarse_compatible hZ F0 hF0 p hp)
    (V.adjointHigherTaylor_coarse_compatible h hK hZ F0 hF0 p hp)
    (t.adjointTaylor_rotation_low_endpoint V hZ F0 hF0 p hp he i j)
    (native_relative_adjoint_rotation_distribution t V h hK hZ p hp i j)

lemma adjointTaylor_balanced_degree_commutator (t : NormalFrameRelativeResponsePacket q)
    (V : t.SymmetricAdjointDomain) {K : ℝ} (h : Elliptic Ω K d.γ) (hK : 0 < K) (hZ : 2 ≤ Z)
    (F0 : SmoothCoefficientMatrix 2)
    (hF0 : ∀ z ∈ Metric.closedBall (0:X) 2,coefficientMatrixField 2 F0 z=1)
    (p : NormalFrameRelativeParameter) (hp : p ∈ V.domain) :
    degreeEndpointCommutator (V.adjointHigherTaylor h hK hZ p) (t.adjointHalfTaylor p)=
      (-(V.degreeFamily h hK hZ p).adjoint).comp
        (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)) := by
  apply balanced_degree_commutator (t.adjointTaylor p) (t.adjointHalfTaylor p)
    (-(V.degreeFamily h hK hZ p).adjoint) (V.adjointHigherTaylor h hK hZ p)
    (V.adjointHalfTaylor_coarse_compatible hZ F0 hF0 p hp)
    (V.adjointHigherTaylor_coarse_compatible h hK hZ F0 hF0 p hp)
  exact half_degree_commutator_adjoint_block (t.forwardTaylor p) (t.adjointTaylor p) (V.taylorPair p hp)
    (V.degreeFamily h hK hZ p) (V.degreeFamily_physical_block h hK hZ p hp)
end ShrinkingSpheres.NormalFrameRelativeResponsePacket
