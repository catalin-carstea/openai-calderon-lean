import Proof.GradedEndpointCommutatorBound
import Proof.GradedHigherEndpointCommutatorBound
noncomputable section
set_option autoImplicit false
namespace ShrinkingSpheres
variable {Hi Mid Lo : Type*} [NormedAddCommGroup Hi] [NormedSpace ℝ Hi]
  [NormedAddCommGroup Mid] [NormedSpace ℝ Mid] [NormedAddCommGroup Lo] [NormedSpace ℝ Lo]

/-- The SAME mixed commutator has bounded compatible realizations at two
genuine Sobolev orders. -/
structure GradedBalancedCommutatorBound (I0 : Mid →L[ℝ] Lo) (I1 : Hi →L[ℝ] Mid)
    (Ga Gb : Mid →L[ℝ] Lo) (Gah Gbh : Hi →L[ℝ] Mid) (B : ℝ) where
  low : Mid →L[ℝ] Lo
  high : Hi →L[ℝ] Mid
  graph : Ga.comp Gbh-Gb.comp Gah=I0.comp high
  balanced : I0.comp high=low.comp I1
  low_bound : ‖low‖ ≤ B
  high_bound : ‖high‖ ≤ B

lemma gradedBalancedCommutatorBound_of_low_high
    {I0 : Mid →L[ℝ] Lo} {I1 : Hi →L[ℝ] Mid}
    {Ga Gb : Mid →L[ℝ] Lo} {Gah Gbh : Hi →L[ℝ] Mid} {BL BH B : ℝ}
    (hL : GradedEndpointCommutatorBound I1 Ga Gb Gah Gbh BL)
    (hH : GradedHigherEndpointCommutatorBound I0 Ga Gb Gah Gbh BH)
    (hBL : BL ≤ B) (hBH : BH ≤ B) :
    Nonempty (GradedBalancedCommutatorBound I0 I1 Ga Gb Gah Gbh B) := by
  obtain ⟨L,hL,hLN⟩ := hL
  obtain ⟨H,hH,hHN⟩ := hH
  exact ⟨{ low := L
           high := H
           graph := hH
           balanced := hH.symm.trans hL
           low_bound := hLN.trans hBL
           high_bound := hHN.trans hBH }⟩
end ShrinkingSpheres
