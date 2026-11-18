import Proof.NativeTaylorGeneratorEndpoints
import Proof.NativeHalfTaylorHigherRegularity
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2600000
set_option maxSynthPendingDepth 30
set_option maxRecDepth 2500
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
open Set Filter
open scoped ContDiff Topology InnerProductSpace
namespace ShrinkingSpheres.NormalFrameRelativeResponsePacket
open OAI.AnisotropicCalderon.DirichletFamily OAI.AnisotropicCalderon.SphereHarmonic
variable {Y Ω : Set X} {d : Data} {y : X} {N : ℕ} {Z CQ : ℝ}
  {q : NormalFrameRelativeCoefficientJetFamily Y Ω d.γ d.g₁ d.expMap y
    (frameVectorLinear d.frame y) (d.radius y) N Z CQ}
  {t : NormalFrameRelativeResponsePacket q}

def SymmetricAdjointDomain.adjointRotationHigherFamily (V : t.SymmetricAdjointDomain)
    {K : ℝ} (h : Elliptic Ω K d.γ) (hK : 0 < K) (hZ : 2 ≤ Z) (i j : I) :
    NormalFrameRelativeParameter → SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ) :=
  normalFrameRelativeAngularDerivative d.γ (V.adjointHigherTaylor h hK hZ) i j

/-- Differentiating the genuine native endpoint square gives the SAME
higher angular commutator endpoint, without identifying Sobolev orders by casts. -/
lemma SymmetricAdjointDomain.adjointRotationHigherFamily_compatible (V : t.SymmetricAdjointDomain)
    (hΩ : IsOpen Ω) {K : ℝ} (h : Elliptic Ω K d.γ) (hK : 0 < K) (hZ : 2 ≤ Z)
    (F0 : SmoothCoefficientMatrix 2)
    (hF0 : ∀ z ∈ Metric.closedBall (0:X) 2,coefficientMatrixField 2 F0 z=1)
    (p : NormalFrameRelativeParameter) (hp : p ∈ V.domain)
    (he : ∀ i j,metricPair d.γ p.1.1 (p.1.2 (axis i)) (p.1.2 (axis j))=if i=j then 1 else 0)
    (i j : I) :
    (sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)).comp
      (V.adjointRotationHigherFamily h hK hZ i j p)=
      (fderiv ℝ t.adjointHalfTaylor p (normalFrameRelativeAngularTangent d.γ p i j)).comp
        (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)) := by
  have hHigh := (V.contDiffOn_adjointHigherTaylor hΩ h hK hZ).contDiffAt
    (V.domainOpen.mem_nhds hp)
  have hLow := V.contDiffOn_adjointHalfTaylor.contDiffAt (V.domainOpen.mem_nhds hp)
  have hCompat : ∀ᶠ x in 𝓝 p,
      (sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)).comp (V.adjointHigherTaylor h hK hZ x)=
        (t.adjointHalfTaylor x).comp (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)) := by
    filter_upwards [V.domainOpen.mem_nhds hp] with x hx
    exact balanced_endpoint_pair_of_coarse _ _ _
      (V.adjointHalfTaylor_coarse_compatible hZ F0 hF0 x hx)
      (V.adjointHigherTaylor_coarse_compatible h hK hZ F0 hF0 x hx)
  have hD := compatible_endpoint_fderiv (V.adjointHigherTaylor h hK hZ) t.adjointHalfTaylor _ _ p
    (normalFrameRelativeAngularTangent d.γ p i j)
    (hHigh.differentiableAt (by simp)) (hLow.differentiableAt (by simp)) hCompat
  simpa only [adjointRotationHigherFamily,normalFrameRelativeAngularDerivative,
    normalFrameRelativeNormalization_eq_self d.γ p he] using hD

lemma SymmetricAdjointDomain.adjointRotationHigherFamily_graph (V : t.SymmetricAdjointDomain)
    (hΩ : IsOpen Ω) {K : ℝ} (h : Elliptic Ω K d.γ) (hK : 0 < K) (hZ : 2 ≤ Z)
    (F0 : SmoothCoefficientMatrix 2)
    (hF0 : ∀ z ∈ Metric.closedBall (0:X) 2,coefficientMatrixField 2 F0 z=1)
    (p : NormalFrameRelativeParameter) (hp : p ∈ V.domain)
    (he : ∀ i j,metricPair d.γ p.1.1 (p.1.2 (axis i)) (p.1.2 (axis j))=if i=j then 1 else 0)
    (i j : I) :
    (sphereSobolevRotationL (1/2:ℝ) i j).comp (V.adjointHigherTaylor h hK hZ p)-
      (t.adjointHalfTaylor p).comp (sphereSobolevRotationL (3/2:ℝ) i j)=
      (sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)).comp
        (V.adjointRotationHigherFamily h hK hZ i j p) :=
  (t.adjointTaylor_balanced_rotation_commutator V h hK hZ F0 hF0 p hp he i j).trans
    (V.adjointRotationHigherFamily_compatible hΩ h hK hZ F0 hF0 p hp he i j).symm

/-- Higher Taylor three-jets and SAME angular commutator two-jets. -/
def SymmetricAdjointDomain.TaylorRotationHigherJetBound (V : t.SymmetricAdjointDomain)
    {K : ℝ} (h : Elliptic Ω K d.γ) (hK : 0 < K) (hZ : 2 ≤ Z)
    (p : NormalFrameRelativeParameter) (B : ℝ) : Prop :=
  SmoothFiniteJetBound (V.adjointHigherTaylor h hK hZ) p 3 B ∧
    ∀ i j : I,SmoothFiniteJetBound (V.adjointRotationHigherFamily h hK hZ i j) p 2 B
end ShrinkingSpheres.NormalFrameRelativeResponsePacket
