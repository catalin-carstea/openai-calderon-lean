import Proof.NativeCenterGradientHalfFamily
import Proof.NativeFullHalfJets
import Proof.RadiusScaledFiniteJets
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxSynthPendingDepth 30
set_option maxRecDepth 2200
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
open Set
open scoped ContDiff Topology
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.DirichletFamily
open OAI.AnisotropicCalderon.SphereHarmonic

lemma NativeRelativeHorizontalTaylorData.centerGradientHalf_three_jet_bound
    {Y Ω : Set X} {d : Data} {y a : X} {F0 : SmoothCoefficientMatrix 2}
    {CQ CI CW CF CA CM CC CH : ℝ}
    (s : NativeRelativeHorizontalTaylorData Y Ω d y F0 CQ CI CW CF CA CM)
    (C : (j : I) → RelativeCenterErrorCoefficientFamily d y a j CC CH)
    (BD CR : ℝ) (hCC : 0 ≤ CC) (hr : 0 < d.radius y)
    (hD : SmoothFiniteJetBound s.response.fullHalfAdjoint ((y,frameVectorLinear d.frame y),0) 3 BD)
    (hR : SmoothFiniteJetBound normalFrameRelativeInverseRadiusFactor ((y,frameVectorLinear d.frame y),0) 3 CR) :
    SmoothFiniteJetBound (s.centerGradientHalfFamily C) ((y,frameVectorLinear d.frame y),0) 3
      ((2^3*CR*halfBoundaryGradientJetBudget 3 BD*CC)*‖a‖*d.radius y) := by
  let p0 : NormalFrameRelativeParameter := ((y,frameVectorLinear d.frame y),0)
  let Q := fun j => (C j).closed
  let H := fun p => halfBoundaryGradientAdjoint (fun j => Q j p) (s.response.fullHalfAdjoint p)
  let B := (2^3*CR*halfBoundaryGradientJetBudget 3 BD*CC)*‖a‖
  have hBQ : 0 ≤ CC*‖a‖*(d.radius y)^2 := by positivity
  have hBudget := halfBoundaryGradientJetBudget_nonneg 3 hD.nonneg
  have hQ (j : I) : ContDiffAt ℝ ∞ (Q j) p0 :=
    (contDiff_commonSupportClosedCoefficientFamily 3 (C j).scalar (C j).smooth (C j).support (C j).compact (C j).supported).contDiffAt
  have hH : SmoothFiniteJetBound H p0 3 (halfBoundaryGradientJetBudget 3 BD*(CC*‖a‖*(d.radius y)^2)) :=
    ⟨by positivity,contDiffAt_halfBoundaryGradientAdjoint Q s.response.fullHalfAdjoint p0 hQ hD.smooth,
      fun n hn => norm_iteratedFDeriv_halfBoundaryGradientAdjoint_le Q s.response.fullHalfAdjoint p0 hQ hD.smooth
        3 (CC*‖a‖*(d.radius y)^2) BD hBQ hD.nonneg (fun j k hk => (C j).joint k hk) hD.bound n hn⟩
  have hScaled := hR.scalar hH
  have hEq : 2^3*CR*(halfBoundaryGradientJetBudget 3 BD*(CC*‖a‖*(d.radius y)^2)) = B*(d.radius y)^2 := by
    dsimp only [B]
    ring
  rw [hEq] at hScaled
  exact hScaled.radius_rescale hr
end ShrinkingSpheres
