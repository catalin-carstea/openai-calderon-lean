import Proof.GradedEndpointCommutatorBound
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace ShrinkingSpheres
variable {Hi Mid Lo F : Type*} [NormedAddCommGroup Hi] [NormedSpace ℝ Hi]
  [NormedAddCommGroup Mid] [NormedSpace ℝ Mid] [NormedAddCommGroup Lo] [NormedSpace ℝ Lo]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Opaque physical endpoint transport. Equality is tested through the
    genuine injective inclusion, with the SAME low maps and norm witness. -/
lemma GradedEndpointCommutatorBound.congr_of_restrictions
    {I : Hi →L[ℝ] Mid} {Ga Gb Ga' Gb' : Mid →L[ℝ] Lo}
    {Gah Gbh Gah' Gbh' : Hi →L[ℝ] Mid} {B : ℝ}
    (h : GradedEndpointCommutatorBound I Ga Gb Gah Gbh B)
    (J : Mid →L[ℝ] F) (hJ : Function.Injective J)
    (ha : Ga=Ga') (hb : Gb=Gb')
    (hah : J.comp Gah=J.comp Gah') (hbh : J.comp Gbh=J.comp Gbh') :
    GradedEndpointCommutatorBound I Ga' Gb' Gah' Gbh' B := by
  have hA : Gah=Gah' := ContinuousLinearMap.ext (fun u => hJ (DFunLike.congr_fun hah u))
  have hB : Gbh=Gbh' := ContinuousLinearMap.ext (fun u => hJ (DFunLike.congr_fun hbh u))
  exact h.congr ha hb hA hB
end ShrinkingSpheres
