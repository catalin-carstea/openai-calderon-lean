import Proof.NativeCenterGradientAngularFields
import Proof.NativeFullRadialAngularRegularity
import Proof.BoundaryGradientAngularJets
import Proof.CoarseAngularDataJetBound
import Proof.CoarseDegreeAssemblyJets
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxSynthPendingDepth 30
set_option maxRecDepth 2500
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
open Set
open scoped ContDiff Topology
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.DirichletFamily
open OAI.AnisotropicCalderon.SphereHarmonic
open OAI.AnisotropicCalderon.ClosedScalarCompatibility
variable {Y Ω : Set X} {d : Data} {y a : X} {F0 : SmoothCoefficientMatrix 2}
  {CQ CI CW CF CA CM CC CH : ℝ}

namespace NativeRelativeHorizontalTaylorData

def centerDegreeDomain
    (s : NativeRelativeHorizontalTaylorData Y Ω d y F0 CQ CI CW CF CA CM)
    (V : s.response.SymmetricAdjointDomain) : Set NormalFrameRelativeParameter :=
  V.domain ∩ {p | 0 < 1+p.2}

lemma centerDegreeDomain_open
    (s : NativeRelativeHorizontalTaylorData Y Ω d y F0 CQ CI CW CF CA CM)
    (V : s.response.SymmetricAdjointDomain) : IsOpen (s.centerDegreeDomain V) :=
  V.domainOpen.inter (isOpen_lt continuous_const (continuous_const.add continuous_snd))
lemma centerDegreeDomain_pointMem
    (s : NativeRelativeHorizontalTaylorData Y Ω d y F0 CQ CI CW CF CA CM)
    (V : s.response.SymmetricAdjointDomain) :
    ((y,frameVectorLinear d.frame y),0) ∈ s.centerDegreeDomain V :=
  ⟨V.pointMem,by norm_num⟩

lemma centerGradientAngularFields_smoothAt
    (s : NativeRelativeHorizontalTaylorData Y Ω d y F0 CQ CI CW CF CA CM)
    (C : (j : I) → RelativeCenterErrorCoefficientFamily d y a j CC CH)
    (V : s.response.SymmetricAdjointDomain) (hΩ : IsOpen Ω) {K : ℝ} (h : Elliptic Ω K d.γ) (hK : 0 < K)
    (p : NormalFrameRelativeParameter) (hp : p ∈ s.centerDegreeDomain V) :
    CoarseAngularFields.SmoothAt (s.centerGradientAngularFields C) p := by
  have hQ (j : I) : ContDiffAt ℝ ∞ (C j).closed p :=
    (contDiff_commonSupportClosedCoefficientFamily 3 (C j).scalar (C j).smooth (C j).support
      (C j).compact (C j).supported).contDiffAt
  have hG := (s.response.fullAdjointAngularFields_smoothAt V hΩ h hK p hp.1).gradient
    (fun j => (C j).closed) hQ
  have hR : ContDiffAt ℝ ∞ normalFrameRelativeInverseRadiusFactor p :=
    (contDiffAt_const.add contDiffAt_snd).inv (ne_of_gt hp.2)
  exact (CoarseAngularFields.SmoothAt.scalar hR hG).const_smul (d.radius y)⁻¹

lemma centerGradientDegree_constraint
    (s : NativeRelativeHorizontalTaylorData Y Ω d y F0 CQ CI CW CF CA CM)
    (C : (j : I) → RelativeCenterErrorCoefficientFamily d y a j CC CH)
    (V : s.response.SymmetricAdjointDomain) {K : ℝ} (h : Elliptic Ω K d.γ) (hK : 0 < K) :
    ∀ p ∈ s.centerDegreeDomain V,∀ z,CoarseDegreeCompatibility.constraintL z
      ((s.centerGradientAngularFields C p).degreeData) = 0 := by
  intro p hp
  exact (mem_simultaneousScalarKernel_iff CoarseDegreeCompatibility.constraintL _).mp
    (s.centerGradientAngularFields_compatible C V h hK p hp.1)

def centerGradientDegreeFamily
    (s : NativeRelativeHorizontalTaylorData Y Ω d y F0 CQ CI CW CF CA CM)
    (C : (j : I) → RelativeCenterErrorCoefficientFamily d y a j CC CH)
    (V : s.response.SymmetricAdjointDomain) {K : ℝ} (h : Elliptic Ω K d.γ) (hK : 0 < K) :
    NormalFrameRelativeParameter → SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ)) :=
  CoarseDegreeCompatibility.halfFamily (fun p => (s.centerGradientAngularFields C p).degreeData)
    (s.centerDegreeDomain V) (s.centerGradientDegree_constraint C V h hK)

lemma contDiffOn_centerGradientDegreeData
    (s : NativeRelativeHorizontalTaylorData Y Ω d y F0 CQ CI CW CF CA CM)
    (C : (j : I) → RelativeCenterErrorCoefficientFamily d y a j CC CH)
    (V : s.response.SymmetricAdjointDomain) (hΩ : IsOpen Ω) {K : ℝ} (h : Elliptic Ω K d.γ) (hK : 0 < K) :
    ContDiffOn ℝ ∞ (fun p => (s.centerGradientAngularFields C p).degreeData) (s.centerDegreeDomain V) := by
  intro p hp
  exact (s.centerGradientAngularFields_smoothAt C V hΩ h hK p hp).degreeData.contDiffWithinAt

lemma contDiffOn_centerGradientDegreeFamily
    (s : NativeRelativeHorizontalTaylorData Y Ω d y F0 CQ CI CW CF CA CM)
    (C : (j : I) → RelativeCenterErrorCoefficientFamily d y a j CC CH)
    (V : s.response.SymmetricAdjointDomain) (hΩ : IsOpen Ω) {K : ℝ} (h : Elliptic Ω K d.γ) (hK : 0 < K) :
    ContDiffOn ℝ ∞ (s.centerGradientDegreeFamily C V h hK) (s.centerDegreeDomain V) :=
  CoarseDegreeCompatibility.contDiffOn_halfFamily _ _ (s.centerDegreeDomain_open V)
    (s.centerGradientDegree_constraint C V h hK) (s.contDiffOn_centerGradientDegreeData C V hΩ h hK)

lemma centerGradientDegreeFamily_physical_block
    (s : NativeRelativeHorizontalTaylorData Y Ω d y F0 CQ CI CW CF CA CM)
    (C : (j : I) → RelativeCenterErrorCoefficientFamily d y a j CC CH)
    (V : s.response.SymmetricAdjointDomain) {K : ℝ} (h : Elliptic Ω K d.γ) (hK : 0 < K)
    (p : NormalFrameRelativeParameter) (hp : p ∈ s.centerDegreeDomain V)
    (m n : ℕ) (z : harmonicSphereSubspace n) :
    sphereSobolevCoefficientL (-(1/2:ℝ)) m
      (s.centerGradientDegreeFamily C V h hK p (sphereSobolevSingleL (1/2:ℝ) n z)) =
        ((m:ℝ)-(n:ℝ)) • coarsePhysicalHarmonicBlock (s.centerGradientAdjointFamily C p) m n z := by
  have hh := CoarseDegreeCompatibility.halfFamily_physical_block
    (fun p => (s.centerGradientAngularFields C p).degreeData) (s.centerDegreeDomain V)
    (s.centerGradientDegree_constraint C V h hK) p hp m n z
  change _ = ((m:ℝ)-(n:ℝ)) • coarsePhysicalHarmonicBlock (s.centerGradientAngularFields C p).operator m n z at hh
  rw [s.centerGradientAngularFields_operator] at hh
  exact hh

end NativeRelativeHorizontalTaylorData
end ShrinkingSpheres
