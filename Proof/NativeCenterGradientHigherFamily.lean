import Proof.NativeCenterGradientHalfFamily
import Proof.HalfDegreeHigherLiftJets
import Proof.HigherHalfPhysicalCompatibility
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2600000
set_option maxSynthPendingDepth 30
set_option maxRecDepth 2200
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
open Set
open scoped ContDiff Topology
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.DirichletFamily
open OAI.AnisotropicCalderon.SphereHarmonic
variable {Y Ω : Set X} {d : Data} {y a : X} {F0 : SmoothCoefficientMatrix 2}
  {CQ CI CW CF CA CM CC CH : ℝ}
namespace NativeRelativeHorizontalTaylorData

def centerGradientHigherFamily
    (s : NativeRelativeHorizontalTaylorData Y Ω d y F0 CQ CI CW CF CA CM)
    (C : (j : I) → RelativeCenterErrorCoefficientFamily d y a j CC CH)
    (V : s.response.SymmetricAdjointDomain) {K : ℝ} (h : Elliptic Ω K d.γ) (hK : 0 < K)
    (p : NormalFrameRelativeParameter) : SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ) :=
  halfDegreeHigherLift (s.centerGradientHalfFamily C p) (s.centerGradientDegreeFamily C V h hK p)

lemma centerGradientHigherFamily_physical_block
    (s : NativeRelativeHorizontalTaylorData Y Ω d y F0 CQ CI CW CF CA CM)
    (C : (j : I) → RelativeCenterErrorCoefficientFamily d y a j CC CH)
    (V : s.response.SymmetricAdjointDomain) {K : ℝ} (h : Elliptic Ω K d.γ) (hK : 0 < K)
    (p : NormalFrameRelativeParameter) (hp : p ∈ s.centerDegreeDomain V)
    (m n : ℕ) (z : harmonicSphereSubspace n) :
    sphereSobolevCoefficientL (1/2:ℝ) m
      (s.centerGradientHigherFamily C V h hK p (sphereSobolevSingleL (3/2:ℝ) n z)) =
      coarsePhysicalHarmonicBlock (s.centerGradientAdjointFamily C p) m n z := by
  have hL := s.centerGradientHalfFamily_physical_block C V p hp.1
  have hS (i j : ℕ) (v : harmonicSphereSubspace j) :
      sphereSobolevCoefficientL (-(1/2:ℝ)) i
        (s.centerGradientDegreeFamily C V h hK p (sphereSobolevSingleL (1/2:ℝ) j v)) =
        ((i:ℝ)-(j:ℝ)) • sphereSobolevCoefficientL (-(1/2:ℝ)) i
          (s.centerGradientHalfFamily C p (sphereSobolevSingleL (1/2:ℝ) j v)) := by
    rw [hL]
    exact s.centerGradientDegreeFamily_physical_block C V h hK p hp i j v
  exact (halfDegreeHigherLift_single_coefficient _ _ hS m n z).trans (hL m n z)

lemma centerGradientHigherFamily_coarse_compatible
    (s : NativeRelativeHorizontalTaylorData Y Ω d y F0 CQ CI CW CF CA CM)
    (C : (j : I) → RelativeCenterErrorCoefficientFamily d y a j CC CH)
    (V : s.response.SymmetricAdjointDomain) {K : ℝ} (h : Elliptic Ω K d.γ) (hK : 0 < K)
    (p : NormalFrameRelativeParameter) (hp : p ∈ s.centerDegreeDomain V) :
    (sphereSobolevInclusionL (1/2:ℝ) 0 (by norm_num)).comp (s.centerGradientHigherFamily C V h hK p) =
      (s.centerGradientAdjointFamily C p).comp (sphereSobolevInclusionL (3/2:ℝ) 1 (by norm_num)) :=
  higher_half_coarse_compatible_of_blocks _ _ (s.centerGradientHigherFamily_physical_block C V h hK p hp)

lemma contDiffOn_centerGradientHigherFamily
    (s : NativeRelativeHorizontalTaylorData Y Ω d y F0 CQ CI CW CF CA CM)
    (C : (j : I) → RelativeCenterErrorCoefficientFamily d y a j CC CH)
    (V : s.response.SymmetricAdjointDomain) (hΩ : IsOpen Ω) {K : ℝ} (h : Elliptic Ω K d.γ) (hK : 0 < K) :
    ContDiffOn ℝ ∞ (s.centerGradientHigherFamily C V h hK) (s.centerDegreeDomain V) := by
  intro p hp
  exact (contDiffAt_halfDegreeHigherLift _ _ p
    ((s.contDiffOn_centerGradientHalfFamily C V).contDiffAt ((s.centerDegreeDomain_open V).mem_nhds hp))
    ((s.contDiffOn_centerGradientDegreeFamily C V hΩ h hK).contDiffAt ((s.centerDegreeDomain_open V).mem_nhds hp))).contDiffWithinAt
end NativeRelativeHorizontalTaylorData
end ShrinkingSpheres
