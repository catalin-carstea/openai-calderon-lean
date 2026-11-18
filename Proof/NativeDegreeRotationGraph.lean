import Proof.AngularPhysicalBlockDerivative
import Proof.HalfRotationDistribution
import Proof.NativeRelativeDegreeHigherData
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2800000
set_option maxSynthPendingDepth 30
set_option maxRecDepth 2500
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter
open scoped ContDiff Topology InnerProductSpace
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.SphereHarmonic
open OAI.AnisotropicCalderon.SmoothSphereRotationProjection
namespace NormalFrameRelativeResponsePacket
variable {Y Ω : Set X} {d : Data} {y : X} {N : ℕ} {Z CQ : ℝ}
  {q : NormalFrameRelativeCoefficientJetFamily Y Ω d.γ d.g₁ d.expMap y
    (frameVectorLinear d.frame y) (d.radius y) N Z CQ}
  {t : NormalFrameRelativeResponsePacket q}

lemma SymmetricAdjointDomain.degreeFamily_eq_on_overlap (V W : t.SymmetricAdjointDomain)
    {K : ℝ} (h : Elliptic Ω K d.γ) (hK : 0 < K) (hZ : 2 ≤ Z)
    (p : NormalFrameRelativeParameter) (hpV : p ∈ V.domain) (hpW : p ∈ W.domain) :
    V.degreeFamily h hK hZ p=W.degreeFamily h hK hZ p := by
  apply sphereSobolev_clm_ext_on_single (1/2:ℝ)
  intro n z
  apply sphereSobolev_ext (-(1/2:ℝ))
  intro m
  rw [V.degreeFamily_physical_block h hK hZ p hpV,W.degreeFamily_physical_block h hK hZ p hpW]

lemma SymmetricAdjointDomain.degreeFamily_germ_eq (V W : t.SymmetricAdjointDomain)
    {K : ℝ} (h : Elliptic Ω K d.γ) (hK : 0 < K) (hZ : 2 ≤ Z)
    (p : NormalFrameRelativeParameter) (hpV : p ∈ V.domain) (hpW : p ∈ W.domain) :
    V.degreeFamily h hK hZ =ᶠ[𝓝 p] W.degreeFamily h hK hZ := by
  filter_upwards [V.domainOpen.mem_nhds hpV,W.domainOpen.mem_nhds hpW] with x hxV hxW
  exact V.degreeFamily_eq_on_overlap W h hK hZ x hxV hxW

/-- The angular derivative of the SAME extracted degree family is its
actual rotation commutator, proved by differentiating exact physical blocks. -/
lemma SymmetricAdjointDomain.degreeFamily_rotation_blocks (V : t.SymmetricAdjointDomain)
    (hΩ : IsOpen Ω) {K : ℝ} (h : Elliptic Ω K d.γ) (hK : 0 < K) (hZ : 2 ≤ Z)
    (p : NormalFrameRelativeParameter) (hp : p ∈ V.domain) (i j : I)
    (m n : ℕ) (z : harmonicSphereSubspace n) :
    sphereSobolevCoefficientL (-(1/2:ℝ)) m
      (normalFrameRelativeAngularDerivative d.γ (V.degreeFamily h hK hZ) i j p
        (sphereSobolevSingleL (1/2:ℝ) n z))=
      harmonicSphereRotation m i j
        (sphereSobolevCoefficientL (-(1/2:ℝ)) m
          (V.degreeFamily h hK hZ p (sphereSobolevSingleL (1/2:ℝ) n z)))-
      sphereSobolevCoefficientL (-(1/2:ℝ)) m
        (V.degreeFamily h hK hZ p (sphereSobolevSingleL (1/2:ℝ) n (harmonicSphereRotation n i j z))) := by
  have hpN := V.normalizationStable p hp
  have hF := (t.contDiffOn_forwardTaylor.contDiffAt (t.domainOpen.mem_nhds (V.sub hpN))).differentiableAt (by simp)
  have hS := ((V.contDiffOn_degreeFamily hΩ h hK hZ).contDiffAt
    (V.domainOpen.mem_nhds hpN)).differentiableAt (by simp)
  have hDerivative := angular_half_block_of_coarse_relation d.γ t.forwardTaylor
    (V.degreeFamily h hK hZ) V.domain V.domainOpen p hpN hF hS
    (fun m n => (m:ℝ)-(n:ℝ)) (fun x hx => V.degreeFamily_physical_block h hK hZ x hx) i j m n z
  rw [V.degreeFamily_physical_block h hK hZ p hp,V.degreeFamily_physical_block h hK hZ p hp,hDerivative]
  have hRotation := coarsePhysicalHarmonicBlock_of_rotation_distribution i j (t.forwardTaylor p)
    (normalFrameRelativeAngularDerivative d.γ t.forwardTaylor i j p)
    (native_relative_forward_rotation_distribution t V h hK hZ p hp i j) m n z
  rw [hRotation]
  simp only [map_smul,smul_sub]

lemma SymmetricAdjointDomain.degreeFamily_rotation_distribution (V : t.SymmetricAdjointDomain)
    (hΩ : IsOpen Ω) {K : ℝ} (h : Elliptic Ω K d.γ) (hK : 0 < K) (hZ : 2 ≤ Z)
    (p : NormalFrameRelativeParameter) (hp : p ∈ V.domain) (i j : I)
    (u : SphereSobolev (3/2:ℝ)) :
    sphereSobolevInclusionL (-(1/2:ℝ)) (-(3/2:ℝ)) (by norm_num)
      (V.degreeFamily h hK hZ p (sphereSobolevRotationL (3/2:ℝ) i j u)+
        normalFrameRelativeAngularDerivative d.γ (V.degreeFamily h hK hZ) i j p
          (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num) u))=
      sphereSobolevRotationL (-(1/2:ℝ)) i j
        (V.degreeFamily h hK hZ p (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num) u)) :=
  half_rotation_distribution_of_physical_blocks i j _ _
    (V.degreeFamily_rotation_blocks hΩ h hK hZ p hp i j) u
end NormalFrameRelativeResponsePacket
end ShrinkingSpheres
