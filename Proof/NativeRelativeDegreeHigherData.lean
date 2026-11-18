import Proof.NativeRelativeDegreeFamilySmooth
import Proof.CoarseDegreeAssemblyJets
import Proof.UniformNativeRelativeSymmetricHigherData
import Proof.UniformRelativeAngularDerivativeJets
import Proof.FintypeFamilyHigherJetBound

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2600000
set_option maxSynthPendingDepth 30
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
open Set Filter
open scoped ContDiff Topology InnerProductSpace
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.SphereHarmonic
open OAI.AnisotropicCalderon.ClosedScalarCompatibility
namespace NormalFrameRelativeResponsePacket
variable {Y Ω : Set X} {d : Data} {y : X} {N : ℕ} {Z C : ℝ}
  {q : NormalFrameRelativeCoefficientJetFamily Y Ω d.γ d.g₁ d.expMap y
    (frameVectorLinear d.frame y) (d.radius y) N Z C}

lemma SymmetricAdjointDomain.degreeData_constraint {t : NormalFrameRelativeResponsePacket q}
    (V : t.SymmetricAdjointDomain) {K : ℝ} (h : Elliptic Ω K d.γ) (hK : 0 < K) (hZ : 2 ≤ Z) :
    ∀ p ∈ V.domain,∀ z,CoarseDegreeCompatibility.constraintL z (t.degreeData p) = 0 := by
  intro p hp
  exact (mem_simultaneousScalarKernel_iff CoarseDegreeCompatibility.constraintL (t.degreeData p)).mp
    (V.degreeData_mem h hK hZ p hp)

def SymmetricAdjointDomain.degreeFamily {t : NormalFrameRelativeResponsePacket q}
    (V : t.SymmetricAdjointDomain) {K : ℝ} (h : Elliptic Ω K d.γ) (hK : 0 < K) (hZ : 2 ≤ Z) :
    NormalFrameRelativeParameter → SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ)) :=
  CoarseDegreeCompatibility.halfFamily t.degreeData V.domain (V.degreeData_constraint h hK hZ)

lemma SymmetricAdjointDomain.contDiffOn_degreeFamily {t : NormalFrameRelativeResponsePacket q}
    (V : t.SymmetricAdjointDomain) (hΩ : IsOpen Ω) {K : ℝ} (h : Elliptic Ω K d.γ) (hK : 0 < K) (hZ : 2 ≤ Z) :
    ContDiffOn ℝ ∞ (V.degreeFamily h hK hZ) V.domain :=
  CoarseDegreeCompatibility.contDiffOn_halfFamily t.degreeData V.domain V.domainOpen
    (V.degreeData_constraint h hK hZ) (V.contDiffOn_degreeData hΩ h hK)

lemma SymmetricAdjointDomain.degreeFamily_physical_block {t : NormalFrameRelativeResponsePacket q}
    (V : t.SymmetricAdjointDomain) {K : ℝ} (h : Elliptic Ω K d.γ) (hK : 0 < K) (hZ : 2 ≤ Z)
    (p : NormalFrameRelativeParameter) (hp : p ∈ V.domain) (m n : ℕ) (z : harmonicSphereSubspace n) :
    sphereSobolevCoefficientL (-(1/2:ℝ)) m
      (V.degreeFamily h hK hZ p (sphereSobolevSingleL (1/2:ℝ) n z)) =
        ((m:ℝ)-(n:ℝ)) • coarsePhysicalHarmonicBlock (t.forwardTaylor p) m n z := by
  exact CoarseDegreeCompatibility.halfFamily_physical_block t.degreeData V.domain
    (V.degreeData_constraint h hK hZ) p hp m n z

/-- A common joint Taylor budget and common angular budgets bound the
    native compatible data without a dimension-dependent sum loss. -/
lemma norm_iteratedFDeriv_degreeData_le (t : NormalFrameRelativeResponsePacket q)
    (p : NormalFrameRelativeParameter) (hF : ContDiffAt ℝ ∞ t.forwardTaylor p)
    (hC : ∀ ij : I × I,ContDiffAt ℝ ∞ (normalFrameRelativeAngularDerivative d.γ t.forwardTaylor ij.1 ij.2) p)
    (hA : ∀ ij : I × I,ContDiffAt ℝ ∞ (normalFrameRelativeAngularDerivative d.γ t.adjointTaylor ij.1 ij.2) p)
    (n : ℕ) (B : ℝ) (hB : 0 ≤ B)
    (hFJet : ‖iteratedFDeriv ℝ n t.forwardTaylor p‖ ≤ B)
    (hCJet : ∀ ij : I × I,‖iteratedFDeriv ℝ n (normalFrameRelativeAngularDerivative d.γ t.forwardTaylor ij.1 ij.2) p‖ ≤ B)
    (hAJet : ∀ ij : I × I,‖iteratedFDeriv ℝ n (normalFrameRelativeAngularDerivative d.γ t.adjointTaylor ij.1 ij.2) p‖ ≤ B) :
    ‖iteratedFDeriv ℝ n t.degreeData p‖ ≤ B := by
  exact norm_iteratedFDeriv_coarseDegreeAssembly_le t.forwardTaylor
    (fun ij => normalFrameRelativeAngularDerivative d.γ t.forwardTaylor ij.1 ij.2)
    (fun ij => normalFrameRelativeAngularDerivative d.γ t.adjointTaylor ij.1 ij.2)
    p hF hC hA n B hB hFJet hCJet hAJet

end NormalFrameRelativeResponsePacket
end ShrinkingSpheres
