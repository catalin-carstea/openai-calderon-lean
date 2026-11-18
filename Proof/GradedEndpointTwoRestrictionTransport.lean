import Proof.GradedEndpointRestrictionTransport
noncomputable section
set_option autoImplicit false
namespace ShrinkingSpheres
variable {Hi Mid Lo F G : Type*} [NormedAddCommGroup Hi] [NormedSpace ℝ Hi]
  [NormedAddCommGroup Mid] [NormedSpace ℝ Mid] [NormedAddCommGroup Lo] [NormedSpace ℝ Lo]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]

/-- Mixed adjoint endpoints may use different genuine output inclusions.
    Both are checked injectively without changing the shared norm witness. -/
lemma GradedEndpointCommutatorBound.congr_of_two_restrictions
    {I : Hi →L[ℝ] Mid} {Ga Gb Ga' Gb' : Mid →L[ℝ] Lo}
    {Gah Gbh Gah' Gbh' : Hi →L[ℝ] Mid} {B : ℝ}
    (h : GradedEndpointCommutatorBound I Ga Gb Gah Gbh B)
    (Ja : Mid →L[ℝ] F) (Jb : Mid →L[ℝ] G) (hJa : Function.Injective Ja) (hJb : Function.Injective Jb)
    (ha : Ga=Ga') (hb : Gb=Gb')
    (hah : Ja.comp Gah=Ja.comp Gah') (hbh : Jb.comp Gbh=Jb.comp Gbh') :
    GradedEndpointCommutatorBound I Ga' Gb' Gah' Gbh' B := by
  have hA : Gah=Gah' := ContinuousLinearMap.ext (fun u => hJa (DFunLike.congr_fun hah u))
  have hB : Gbh=Gbh' := ContinuousLinearMap.ext (fun u => hJb (DFunLike.congr_fun hbh u))
  exact h.congr ha hb hA hB
end ShrinkingSpheres
