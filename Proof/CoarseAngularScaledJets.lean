import Proof.NormalFrameScaledJetBounds
import Proof.RadiusScaledFiniteJets
import Proof.CoarseAngularFieldJets
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
open scoped ContDiff
namespace ShrinkingSpheres
namespace CoarseAngularFields.JetBound

lemma scaled_parameter_three {F : NormalFrameRelativeParameter → CoarseAngularFields}
    {y : X} {L : X →L[ℝ] X} {B β : ℝ} (hβ : 1 ≤ β)
    (hF : CoarseAngularFields.JetBound F ((y,L),0) 3 B) :
    CoarseAngularFields.JetBound (F ∘ normalFrameRelativeScaledParameter β y) ((0,L),0) 3 (6*B) :=
  ⟨normalFrame_scaled_parameter_three_jet_bound β hβ y L hF.operator,
    normalFrame_scaled_parameter_three_jet_bound β hβ y L hF.adjoint,
    (fun ij => normalFrame_scaled_parameter_three_jet_bound β hβ y L (hF.angular ij)),
    (fun ij => normalFrame_scaled_parameter_three_jet_bound β hβ y L (hF.angularAdjoint ij))⟩

lemma radius_rescale {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    {F : P → CoarseAngularFields} {p : P} {N : ℕ} {B r : ℝ}
    (hF : CoarseAngularFields.JetBound F p N (B*r^2)) (hr : 0 < r) :
    CoarseAngularFields.JetBound (fun x => (F x).smul r⁻¹) p N (B*r) :=
  ⟨hF.operator.radius_rescale hr,hF.adjoint.radius_rescale hr,
    (fun ij => (hF.angular ij).radius_rescale hr),(fun ij => (hF.angularAdjoint ij).radius_rescale hr)⟩
end CoarseAngularFields.JetBound
end ShrinkingSpheres
