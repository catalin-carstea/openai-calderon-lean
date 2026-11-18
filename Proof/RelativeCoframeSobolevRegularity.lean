import Proof.RelativeCoframeSobolevMultiplier
import Proof.RelativeCoframeSmoothDomain
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
open Set
open scoped ContDiff
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.SphereHarmonic
lemma Elliptic.contDiffOn_relativeCoframeSobolevMultiplier {Ω : Set X} (hΩ : IsOpen Ω)
    {K : ℝ} {g : MetricField} (h : Elliptic Ω K g) (hK : 0 < K) (s : ℝ) (a : X) :
    ContDiffOn ℝ ∞ (relativeCoframeNormalSobolevL s g a) (normalFrameRelativePositiveDomain Ω) := by
  apply ContDiffOn.sum
  intro j hj
  exact (h.contDiffOn_relativeCoframeValue hΩ hK a j).smul contDiffOn_const
end ShrinkingSpheres
