import Proof.ScaledTwoJetProductBounds

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
open scoped ContDiff Topology
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.SphereHarmonic

/-- Sharp small scalar jets cancel the beta growth of the actual bounded
correction's covariant jets in the four genuine product-rule terms. -/
lemma coarse_scaled_two_jet_product_bounds
    (F Sb Sc T : SphereSobolev 1 →L[ℝ] SphereSobolev 0)
    (w wb wc wbc B C ε β : ℝ) (hB : 0 ≤ B) (hε : 0 ≤ ε) (hβ : 0 < β)
    (hw : |w| ≤ B*ε/β^2) (hwb : |wb| ≤ B*ε/β) (hwc : |wc| ≤ B*ε/β)
    (hwbc : |wbc| ≤ B*ε)
    (hF : ‖F‖ ≤ C) (hSb : ‖Sb‖ ≤ C*β) (hSc : ‖Sc‖ ≤ C*β) (hT : ‖T‖ ≤ C*β^2) :
    ‖w • F‖ ≤ B*C*ε/β^2 ∧
      ‖w • Sb+wb • F‖ ≤ 2*B*C*ε/β ∧
      ‖(w • T+wc • Sb)+(wb • Sc+wbc • F)‖ ≤ 4*B*C*ε := by
  exact scaled_two_jet_product_bounds F Sb Sc T w wb wc wbc B C ε β hB hε hβ
    hw hwb hwc hwbc hF hSb hSc hT

end ShrinkingSpheres
