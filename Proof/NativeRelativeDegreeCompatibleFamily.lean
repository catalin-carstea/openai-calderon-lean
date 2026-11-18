import Proof.RelativeAngularDerivativeCurve
import Proof.RotationGraphHarmonicBlocks
import Proof.NativeRelativeForwardRotationGraph
import Proof.NativeRelativeAdjointRotationGraph
import Proof.RelativeAngularNormalizationJets
import Proof.CoarseDegreeFamilyJets
import Proof.OperatorAdjointDerivativePairing

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 2000
set_option maxSynthPendingDepth 30
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter
open scoped ContDiff Topology InnerProductSpace
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.SphereHarmonic
open OAI.AnisotropicCalderon.SmoothSphereRotationProjection

lemma contDiffAt_relativeAngularDerivative
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (g : MetricField) (F : NormalFrameRelativeParameter → E) (p : NormalFrameRelativeParameter)
    (hF : ContDiffAt ℝ ∞ F (normalFrameRelativeNormalization g p))
    (hQ : ContDiffAt ℝ ∞ (normalFrameRelativeNormalization g) p) (i j : I) :
    ContDiffAt ℝ ∞ (normalFrameRelativeAngularDerivative g F i j) p := by
  have hTan : ContDiffAt ℝ ∞ (fun p => normalFrameRelativeAngularTangent g p i j) p :=
    (relativeAngularTangentFromFrameL i j).contDiff.contDiffAt.comp p hQ.fst.snd
  exact ((hF.fderiv_right (m:=∞) (by simp)).comp p hQ).clm_apply hTan

namespace NormalFrameRelativeResponsePacket
variable {Y Ω : Set X} {d : Data} {y : X} {N : ℕ} {Z C : ℝ}
  {q : NormalFrameRelativeCoefficientJetFamily Y Ω d.γ d.g₁ d.expMap y
    (frameVectorLinear d.frame y) (d.radius y) N Z C}

def degreeData (t : NormalFrameRelativeResponsePacket q) (p : NormalFrameRelativeParameter) :
    CoarseDegreeCompatibility.CoarseDegreeData :=
  (t.forwardTaylor p,((fun ij => normalFrameRelativeAngularDerivative d.γ t.forwardTaylor ij.1 ij.2 p),
    (fun ij => normalFrameRelativeAngularDerivative d.γ t.adjointTaylor ij.1 ij.2 p)))

theorem SymmetricAdjointDomain.angularPair {t : NormalFrameRelativeResponsePacket q}
    (V : t.SymmetricAdjointDomain) (p : NormalFrameRelativeParameter) (hp : p ∈ V.domain) (i j : I) :
    ∀ u v : SphereSobolev 1,
      ⟪normalFrameRelativeAngularDerivative d.γ t.forwardTaylor i j p u,
        sphereSobolevInclusionL 1 0 (by norm_num) v⟫_ℝ =
      ⟪sphereSobolevInclusionL 1 0 (by norm_num) u,
        normalFrameRelativeAngularDerivative d.γ t.adjointTaylor i j p v⟫_ℝ := by
  let c := normalFrameRelativeAngularCurve d.γ p i j
  have hpN := V.normalizationStable p hp
  have hZero : c 0 = normalFrameRelativeNormalization d.γ p := normalFrameRelativeAngularCurve_zero d.γ p i j
  have hCurve := hasDerivAt_normalFrameRelativeAngularCurve d.γ p i j
  have hF := (t.contDiffOn_forwardTaylor.contDiffAt (t.domainOpen.mem_nhds (V.sub hpN))).differentiableAt (by simp)
  have hA := (t.contDiffOn_adjointTaylor.contDiffAt (t.domainOpen.mem_nhds (V.sub hpN))).differentiableAt (by simp)
  have hCF := hasDerivAt_relativeAngularFamily d.γ t.forwardTaylor p i j hF
  have hCA := hasDerivAt_relativeAngularFamily d.γ t.adjointTaylor p i j hA
  have h0V : c 0 ∈ V.domain := by rw [hZero];exact hpN
  have hEvent : ∀ᶠ θ in 𝓝 (0:ℝ),c θ ∈ V.domain :=
    hCurve.continuousAt.eventually (V.domainOpen.mem_nhds h0V)
  exact operator_derivative_adjoint_pairing _ _ _ _ hCF hCA
    (hEvent.mono (fun θ hθ => V.taylorPair (c θ) hθ))

theorem SymmetricAdjointDomain.degreeData_mem {t : NormalFrameRelativeResponsePacket q}
    (V : t.SymmetricAdjointDomain) {K : ℝ} (h : Elliptic Ω K d.γ) (hK : 0 < K) (hZ : 2 ≤ Z)
    (p : NormalFrameRelativeParameter) (hp : p ∈ V.domain) :
    t.degreeData p ∈ CoarseDegreeCompatibility.compatibleData := by
  apply (CoarseDegreeCompatibility.mem_compatibleData_iff _).mpr
  constructor
  · intro ij m n z
    exact coarsePhysicalHarmonicBlock_of_rotation_distribution ij.1 ij.2
      (t.forwardTaylor p) (normalFrameRelativeAngularDerivative d.γ t.forwardTaylor ij.1 ij.2 p)
      (native_relative_forward_rotation_distribution t V h hK hZ p hp ij.1 ij.2) m n z
  · intro ij
    exact V.angularPair p hp ij.1 ij.2


end NormalFrameRelativeResponsePacket
end ShrinkingSpheres
