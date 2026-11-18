import Proof.NativeFirstErrorAngularFields
import Proof.CoarseDegreeFamilyJets
import Proof.CoarseDegreeAssemblyJets
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxSynthPendingDepth 30
set_option maxRecDepth 2200
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
open Set Filter
open scoped ContDiff Topology
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.DirichletFamily
open OAI.AnisotropicCalderon.SphereHarmonic
open OAI.AnisotropicCalderon.ClosedScalarCompatibility
variable {Y Ω : Set X} {d : Data} {y a : X} {F0 : SmoothCoefficientMatrix 2}
  {CQ CI CW CF CA CM CC CH : ℝ}
namespace NativeRelativeHorizontalTaylorData

lemma firstErrorDegree_constraint
    (s : NativeRelativeHorizontalTaylorData Y Ω d y F0 CQ CI CW CF CA CM)
    (C : (j : I) → RelativeCenterErrorCoefficientFamily d y a j CC CH)
    (V : s.response.SymmetricAdjointDomain) {K : ℝ} (h : Elliptic Ω K d.γ) (hK : 0 < K) :
    ∀ p ∈ s.centerDegreeDomain V,∀ z,CoarseDegreeCompatibility.constraintL z
      ((s.firstErrorAngularFields C p).degreeData) = 0 := by
  intro p hp
  exact (mem_simultaneousScalarKernel_iff CoarseDegreeCompatibility.constraintL _).mp
    (s.firstErrorAngularFields_compatible C V h hK p hp.1)

def firstErrorDegreeFamily
    (s : NativeRelativeHorizontalTaylorData Y Ω d y F0 CQ CI CW CF CA CM)
    (C : (j : I) → RelativeCenterErrorCoefficientFamily d y a j CC CH)
    (V : s.response.SymmetricAdjointDomain) {K : ℝ} (h : Elliptic Ω K d.γ) (hK : 0 < K) :
    NormalFrameRelativeParameter → SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ)) :=
  CoarseDegreeCompatibility.halfFamily (fun p => (s.firstErrorAngularFields C p).degreeData)
    (s.centerDegreeDomain V) (s.firstErrorDegree_constraint C V h hK)

lemma contDiffOn_firstErrorDegreeData
    (s : NativeRelativeHorizontalTaylorData Y Ω d y F0 CQ CI CW CF CA CM)
    (C : (j : I) → RelativeCenterErrorCoefficientFamily d y a j CC CH)
    (V : s.response.SymmetricAdjointDomain) (hY : IsOpen Y) (hΩ : IsOpen Ω)
    {K : ℝ} (h : Elliptic Ω K d.γ) (hK : 0 < K)
    {floor c₀ : ℝ} {Cj : Fin 9 → ℝ} (hProfile : Profile Y d.γ d.frame d.radius floor c₀ Cj) :
    ContDiffOn ℝ ∞ (fun p => (s.firstErrorAngularFields C p).degreeData) (s.centerDegreeDomain V) := by
  intro p hp
  exact (s.firstErrorAngularFields_smoothAt C V hY hΩ h hK hProfile p hp).degreeData.contDiffWithinAt

lemma contDiffOn_firstErrorDegreeFamily
    (s : NativeRelativeHorizontalTaylorData Y Ω d y F0 CQ CI CW CF CA CM)
    (C : (j : I) → RelativeCenterErrorCoefficientFamily d y a j CC CH)
    (V : s.response.SymmetricAdjointDomain) (hY : IsOpen Y) (hΩ : IsOpen Ω)
    {K : ℝ} (h : Elliptic Ω K d.γ) (hK : 0 < K)
    {floor c₀ : ℝ} {Cj : Fin 9 → ℝ} (hProfile : Profile Y d.γ d.frame d.radius floor c₀ Cj) :
    ContDiffOn ℝ ∞ (s.firstErrorDegreeFamily C V h hK) (s.centerDegreeDomain V) :=
  CoarseDegreeCompatibility.contDiffOn_halfFamily _ _ (s.centerDegreeDomain_open V)
    (s.firstErrorDegree_constraint C V h hK) (s.contDiffOn_firstErrorDegreeData C V hY hΩ h hK hProfile)

lemma firstErrorDegreeFamily_physical_block
    (s : NativeRelativeHorizontalTaylorData Y Ω d y F0 CQ CI CW CF CA CM)
    (C : (j : I) → RelativeCenterErrorCoefficientFamily d y a j CC CH)
    (V : s.response.SymmetricAdjointDomain) {K : ℝ} (h : Elliptic Ω K d.γ) (hK : 0 < K)
    (p : NormalFrameRelativeParameter) (hp : p ∈ s.centerDegreeDomain V)
    (m n : ℕ) (z : harmonicSphereSubspace n) :
    sphereSobolevCoefficientL (-(1/2:ℝ)) m
      (s.firstErrorDegreeFamily C V h hK p (sphereSobolevSingleL (1/2:ℝ) n z)) =
        ((m:ℝ)-(n:ℝ)) • coarsePhysicalHarmonicBlock (s.firstAdjointErrorFamily C p) m n z := by
  have hh := CoarseDegreeCompatibility.halfFamily_physical_block
    (fun p => (s.firstErrorAngularFields C p).degreeData) (s.centerDegreeDomain V)
    (s.firstErrorDegree_constraint C V h hK) p hp m n z
  change _ = ((m:ℝ)-(n:ℝ)) • coarsePhysicalHarmonicBlock (s.firstErrorAngularFields C p).operator m n z at hh
  rw [s.firstErrorAngularFields_operator] at hh
  exact hh
end NativeRelativeHorizontalTaylorData
end ShrinkingSpheres
