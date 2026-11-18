import Proof.NativeDegreeRotationGraph
import Proof.HalfRotationAdjointGraph
import Proof.RotationHighLiftLinearMap
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2600000
set_option maxSynthPendingDepth 30
set_option maxRecDepth 2400
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter
open scoped ContDiff Topology InnerProductSpace
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.SphereHarmonic
namespace NormalFrameRelativeResponsePacket
variable {Y Ω : Set X} {d : Data} {y : X} {N : ℕ} {Z CQ : ℝ}
  {q : NormalFrameRelativeCoefficientJetFamily Y Ω d.γ d.g₁ d.expMap y
    (frameVectorLinear d.frame y) (d.radius y) N Z CQ}
  {t : NormalFrameRelativeResponsePacket q}

def SymmetricAdjointDomain.degreeHigherFamily (V : t.SymmetricAdjointDomain)
    {K : ℝ} (h : Elliptic Ω K d.γ) (hK : 0 < K) (hZ : 2 ≤ Z)
    (p : NormalFrameRelativeParameter) : SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ) :=
  rotationHighLiftDataL (V.degreeFamily h hK hZ p,
    fun ij => normalFrameRelativeAngularDerivative d.γ (V.degreeFamily h hK hZ) ij.1 ij.2 p)

def SymmetricAdjointDomain.adjointDegreeHigherFamily (V : t.SymmetricAdjointDomain)
    {K : ℝ} (h : Elliptic Ω K d.γ) (hK : 0 < K) (hZ : 2 ≤ Z)
    (p : NormalFrameRelativeParameter) : SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ) :=
  rotationHighLiftDataL ((V.degreeFamily h hK hZ p).adjoint,
    fun ij => (normalFrameRelativeAngularDerivative d.γ (V.degreeFamily h hK hZ) ij.1 ij.2 p).adjoint)

lemma SymmetricAdjointDomain.degreeHigherFamily_compatible (V : t.SymmetricAdjointDomain)
    (hΩ : IsOpen Ω) {K : ℝ} (h : Elliptic Ω K d.γ) (hK : 0 < K) (hZ : 2 ≤ Z)
    (p : NormalFrameRelativeParameter) (hp : p ∈ V.domain) :
    (sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)).comp (V.degreeHigherFamily h hK hZ p)=
      (V.degreeFamily h hK hZ p).comp (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)) := by
  rw [degreeHigherFamily,rotationHighLiftDataL_apply]
  exact sphereSobolevRotationCommutatorHighLiftL_lower_compatibility _ _
    (fun u i j => V.degreeFamily_rotation_distribution hΩ h hK hZ p hp i j u)

lemma SymmetricAdjointDomain.adjointDegreeHigherFamily_compatible (V : t.SymmetricAdjointDomain)
    (hΩ : IsOpen Ω) {K : ℝ} (h : Elliptic Ω K d.γ) (hK : 0 < K) (hZ : 2 ≤ Z)
    (p : NormalFrameRelativeParameter) (hp : p ∈ V.domain) :
    (sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)).comp (V.adjointDegreeHigherFamily h hK hZ p)=
      (V.degreeFamily h hK hZ p).adjoint.comp (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)) := by
  rw [adjointDegreeHigherFamily,rotationHighLiftDataL_apply]
  exact sphereSobolevRotationCommutatorHighLiftL_lower_compatibility _ _
    (fun u i j => half_rotation_distribution_adjoint i j _ _
      (V.degreeFamily_rotation_distribution hΩ h hK hZ p hp i j) u)
/-- Joint jets of both genuine higher degree-commutator endpoints. -/
def SymmetricAdjointDomain.HigherDegreeJetBound (V : t.SymmetricAdjointDomain)
    {K : ℝ} (h : Elliptic Ω K d.γ) (hK : 0 < K) (hZ : 2 ≤ Z)
    (p : NormalFrameRelativeParameter) (J : ℕ) (B : ℝ) : Prop :=
  SmoothFiniteJetBound (V.degreeHigherFamily h hK hZ) p J B ∧
    SmoothFiniteJetBound (V.adjointDegreeHigherFamily h hK hZ) p J B

end NormalFrameRelativeResponsePacket
end ShrinkingSpheres
