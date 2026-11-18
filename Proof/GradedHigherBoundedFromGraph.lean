import Proof.GradedBoundedRemainderAlgebra
import Proof.HigherBoundedRemainderCompatibility
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
namespace ShrinkingSpheres
variable {Hi Mid Lo : Type*} [NormedAddCommGroup Hi] [NormedSpace ℝ Hi]
  [NormedAddCommGroup Mid] [NormedSpace ℝ Mid] [NormedAddCommGroup Lo] [NormedSpace ℝ Lo]

lemma graded_higher_commutator_bounded_from_graph
    (I1 : Hi →L[ℝ] Mid) (I0 : Mid →L[ℝ] Lo)
    (Ga Gb : Mid →L[ℝ] Lo) (Gah Gbh KH : Hi →L[ℝ] Mid)
    (Za Zb : Mid →L[ℝ] Mid) (Zan Zbn : Lo →L[ℝ] Lo) (Zah Zbh : Hi →L[ℝ] Hi)
    (hK : Ga.comp Gbh-Gb.comp Gah=I0.comp KH)
    (hGa : I0.comp Gah=Ga.comp I1) (hGb : I0.comp Gbh=Gb.comp I1)
    (hZa : I0.comp Za=Zan.comp I0) (hZb : I0.comp Zb=Zbn.comp I0)
    (hZah : I1.comp Zah=Za.comp I1) (hZbh : I1.comp Zbh=Zb.comp I1) :
    (Ga+Zan.comp I0).comp (Gbh+Zb.comp I1)-(Gb+Zbn.comp I0).comp (Gah+Za.comp I1)=
      I0.comp (KH+boundedRemainderCommutatorL I1 Gah Gbh Zah Zbh Za Zb) := by
  have hExpand := graded_bounded_remainder_expansion I1 I0 Ga Gb Gah Gbh Za Zb Zan Zbn hGa hGb
  have hBounded := boundedRemainderCommutatorL_compatible I1 I0 Ga Gb Gah Gbh Za Zb Zan Zbn Zah Zbh
    hGa hGb hZa hZb hZah hZbh
  calc
    _ = (Ga.comp Gbh-Gb.comp Gah)+(boundedRemainderCommutatorL I0 Ga Gb Za Zb Zan Zbn).comp I1 := hExpand
    _ = I0.comp KH+I0.comp (boundedRemainderCommutatorL I1 Gah Gbh Zah Zbh Za Zb) :=
      congrArg₂ (fun U V : Hi →L[ℝ] Lo => U+V) hK hBounded.symm
    _ = _ := (ContinuousLinearMap.comp_add _ _ _).symm
end ShrinkingSpheres
