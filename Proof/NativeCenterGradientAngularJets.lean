import Proof.NativeCenterGradientAngularFields
import Proof.BoundaryGradientAngularJets
import Proof.CoarseAngularDataJetBound
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2600000
set_option maxSynthPendingDepth 30
set_option maxRecDepth 2500
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set
open scoped ContDiff Topology
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.DirichletFamily
open OAI.AnisotropicCalderon.SphereHarmonic

lemma NativeRelativeHorizontalTaylorData.centerGradientAngularFields_jet_bound
    {Y Ω : Set X} {d : Data} {y a : X} {F0 : SmoothCoefficientMatrix 2}
    {CQ CI CW CF CA CM CC CH : ℝ}
    (s : NativeRelativeHorizontalTaylorData Y Ω d y F0 CQ CI CW CF CA CM)
    (C : (j : I) → RelativeCenterErrorCoefficientFamily d y a j CC CH)
    (BD CR : ℝ) (hCC : 0 ≤ CC) (hr : 0 < d.radius y)
    (hD : CoarseAngularFields.JetBound s.response.fullAdjointAngularFields
      ((y,frameVectorLinear d.frame y),0) 3 BD)
    (hR : SmoothFiniteJetBound normalFrameRelativeInverseRadiusFactor
      ((y,frameVectorLinear d.frame y),0) 3 CR) :
    CoarseAngularFields.JetBound (s.centerGradientAngularFields C)
      ((y,frameVectorLinear d.frame y),0) 3
      ((2^3*CR*boundaryGradientAngularJetBudget 3 BD*CC)*‖a‖*d.radius y) := by
  let p0 : NormalFrameRelativeParameter := ((y,frameVectorLinear d.frame y),0)
  have hQ (j : I) : SmoothFiniteJetBound (C j).closed p0 3 (CC*‖a‖*(d.radius y)^2) :=
    ⟨by positivity,(contDiff_commonSupportClosedCoefficientFamily 3 (C j).scalar (C j).smooth
      (C j).support (C j).compact (C j).supported).contDiffAt,(C j).joint⟩
  have hG := hD.gradient (fun j => (C j).closed) hQ
  have hAll := (CoarseAngularFields.JetBound.scalar hR hG).const_smul (d.radius y)⁻¹
  rw [abs_of_pos (inv_pos.mpr hr)] at hAll
  have hBudget : (d.radius y)⁻¹*(2^3*CR*(boundaryGradientAngularJetBudget 3 BD*(CC*‖a‖*(d.radius y)^2))) =
      (2^3*CR*boundaryGradientAngularJetBudget 3 BD*CC)*‖a‖*d.radius y := by field_simp
  rw [hBudget] at hAll
  exact hAll
end ShrinkingSpheres
