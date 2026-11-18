import Proof.GradedLinearRemainderCommutator
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option maxSynthPendingDepth 30
namespace ShrinkingSpheres
variable {Hi Mid Lo : Type*} [NormedAddCommGroup Hi] [NormedSpace ℝ Hi]
  [NormedAddCommGroup Mid] [NormedSpace ℝ Mid] [NormedAddCommGroup Lo] [NormedSpace ℝ Lo]

/-- The six bounded-remainder words represent the SAME low remainder
    through actual higher, middle and lower inclusion squares. -/
lemma boundedRemainderCommutatorL_compatible
    (I1 : Hi →L[ℝ] Mid) (I0 : Mid →L[ℝ] Lo)
    (Ga Gb : Mid →L[ℝ] Lo) (Gah Gbh : Hi →L[ℝ] Mid)
    (Za Zb : Mid →L[ℝ] Mid) (Zan Zbn : Lo →L[ℝ] Lo) (Zah Zbh : Hi →L[ℝ] Hi)
    (hGa : I0.comp Gah=Ga.comp I1) (hGb : I0.comp Gbh=Gb.comp I1)
    (hZa : I0.comp Za=Zan.comp I0) (hZb : I0.comp Zb=Zbn.comp I0)
    (hZah : I1.comp Zah=Za.comp I1) (hZbh : I1.comp Zbh=Zb.comp I1) :
    I0.comp (boundedRemainderCommutatorL I1 Gah Gbh Zah Zbh Za Zb)=
      (boundedRemainderCommutatorL I0 Ga Gb Za Zb Zan Zbn).comp I1 := by
  have hGVa (u : Hi) : I0 (Gah u)=Ga (I1 u) := DFunLike.congr_fun hGa u
  have hGVb (u : Hi) : I0 (Gbh u)=Gb (I1 u) := DFunLike.congr_fun hGb u
  have hZVa (u : Mid) : I0 (Za u)=Zan (I0 u) := DFunLike.congr_fun hZa u
  have hZVb (u : Mid) : I0 (Zb u)=Zbn (I0 u) := DFunLike.congr_fun hZb u
  have hZHVa (u : Hi) : I1 (Zah u)=Za (I1 u) := DFunLike.congr_fun hZah u
  have hZHVb (u : Hi) : I1 (Zbh u)=Zb (I1 u) := DFunLike.congr_fun hZbh u
  apply ContinuousLinearMap.ext
  intro u
  simp only [boundedRemainderCommutatorL,ContinuousLinearMap.comp_apply,
    _root_.add_apply,_root_.sub_apply,ContinuousLinearMap.map_add,ContinuousLinearMap.map_sub,
    hGVa,hGVb,hZVa,hZVb,hZHVa,hZHVb]

/-- Conditional higher caller for the complete commutator. The additional
    premises are precisely the bounded remainders' genuine higher squares. -/
lemma graded_higher_commutator_add_bounded_remainders
    (I1 : Hi →L[ℝ] Mid) (I0 : Mid →L[ℝ] Lo)
    (Ga Gb KL : Mid →L[ℝ] Lo) (Gah Gbh KH : Hi →L[ℝ] Mid)
    (Za Zb : Mid →L[ℝ] Mid) (Zan Zbn : Lo →L[ℝ] Lo) (Zah Zbh : Hi →L[ℝ] Hi)
    (hK : Ga.comp Gbh-Gb.comp Gah=KL.comp I1) (hKH : I0.comp KH=KL.comp I1)
    (hGa : I0.comp Gah=Ga.comp I1) (hGb : I0.comp Gbh=Gb.comp I1)
    (hZa : I0.comp Za=Zan.comp I0) (hZb : I0.comp Zb=Zbn.comp I0)
    (hZah : I1.comp Zah=Za.comp I1) (hZbh : I1.comp Zbh=Zb.comp I1) :
    (Ga+Zan.comp I0).comp (Gbh+Zb.comp I1)-
      (Gb+Zbn.comp I0).comp (Gah+Za.comp I1)=
    I0.comp (KH+boundedRemainderCommutatorL I1 Gah Gbh Zah Zbh Za Zb) := by
  have hFull := graded_commutator_add_bounded_remainders I1 I0 Ga Gb KL Gah Gbh Za Zb Zan Zbn hK hGa hGb
  have hBounded := boundedRemainderCommutatorL_compatible I1 I0 Ga Gb Gah Gbh Za Zb Zan Zbn Zah Zbh
    hGa hGb hZa hZb hZah hZbh
  calc
    _ = (KL+boundedRemainderCommutatorL I0 Ga Gb Za Zb Zan Zbn).comp I1 := hFull
    _ = (KL.comp I1)+(boundedRemainderCommutatorL I0 Ga Gb Za Zb Zan Zbn).comp I1 :=
      ContinuousLinearMap.add_comp _ _ _
    _ = I0.comp KH+I0.comp (boundedRemainderCommutatorL I1 Gah Gbh Zah Zbh Za Zb) :=
      congrArg₂ (fun U V : Hi →L[ℝ] Lo => U+V) hKH.symm hBounded.symm
    _ = _ := (ContinuousLinearMap.comp_add _ _ _).symm
end ShrinkingSpheres
