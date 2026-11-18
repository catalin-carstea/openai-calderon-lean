import Proof.GradedHigherBoundedFromGraph
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace ShrinkingSpheres
variable {Hi Mid Lo : Type*} [NormedAddCommGroup Hi] [NormedSpace ℝ Hi]
  [NormedAddCommGroup Mid] [NormedSpace ℝ Mid] [NormedAddCommGroup Lo] [NormedSpace ℝ Lo]

/-- One shared genuine higher witness supplies both its graph and norm. -/
def GradedHigherEndpointCommutatorBound (I0 : Mid →L[ℝ] Lo) (Ga Gb : Mid →L[ℝ] Lo)
    (Gah Gbh : Hi →L[ℝ] Mid) (B : ℝ) : Prop :=
  ∃ S : Hi →L[ℝ] Mid,Ga.comp Gbh-Gb.comp Gah=I0.comp S ∧ ‖S‖ ≤ B

lemma GradedHigherEndpointCommutatorBound.mono
    {I0 : Mid →L[ℝ] Lo} {Ga Gb : Mid →L[ℝ] Lo} {Gah Gbh : Hi →L[ℝ] Mid} {B B' : ℝ}
    (h : GradedHigherEndpointCommutatorBound I0 Ga Gb Gah Gbh B) (hB : B ≤ B') :
    GradedHigherEndpointCommutatorBound I0 Ga Gb Gah Gbh B' := by
  obtain ⟨S,hS,hN⟩ := h
  exact ⟨S,hS,hN.trans hB⟩

lemma GradedHigherEndpointCommutatorBound.congr
    {I0 : Mid →L[ℝ] Lo} {Ga Gb Ga' Gb' : Mid →L[ℝ] Lo}
    {Gah Gbh Gah' Gbh' : Hi →L[ℝ] Mid} {B : ℝ}
    (h : GradedHigherEndpointCommutatorBound I0 Ga Gb Gah Gbh B)
    (ha : Ga=Ga') (hb : Gb=Gb') (hah : Gah=Gah') (hbh : Gbh=Gbh') :
    GradedHigherEndpointCommutatorBound I0 Ga' Gb' Gah' Gbh' B := by
  subst Ga';subst Gb';subst Gah';subst Gbh'
  exact h

lemma GradedHigherEndpointCommutatorBound.congr_of_restrictions
    {Other : Type*} [NormedAddCommGroup Other] [NormedSpace ℝ Other]
    {I0 : Mid →L[ℝ] Lo} (J : Mid →L[ℝ] Other)
    {Ga Gb Ga' Gb' : Mid →L[ℝ] Lo} {Gah Gbh Ha Hb : Hi →L[ℝ] Mid} {B : ℝ}
    (h : GradedHigherEndpointCommutatorBound I0 Ga Gb Gah Gbh B)
    (ha : Ga=Ga') (hb : Gb=Gb')
    (hI : Function.Injective I0) (hJ : Function.Injective J)
    (hA : I0.comp Ha=I0.comp Gah) (hB : J.comp Hb=J.comp Gbh) :
    GradedHigherEndpointCommutatorBound I0 Ga' Gb' Ha Hb B := by
  have hAh : Gah=Ha := by
    ext u
    exact hI (DFunLike.congr_fun hA.symm u)
  have hBh : Gbh=Hb := by
    ext u
    exact hJ (DFunLike.congr_fun hB.symm u)
  exact h.congr ha hb hAh hBh

lemma GradedHigherEndpointCommutatorBound.add_bounded_linear
    {I0 : Mid →L[ℝ] Lo} (I1 : Hi →L[ℝ] Mid)
    {Ga Gb : Mid →L[ℝ] Lo} {Gah Gbh : Hi →L[ℝ] Mid} {B : ℝ}
    (h : GradedHigherEndpointCommutatorBound I0 Ga Gb Gah Gbh B)
    (Za Zb : Mid →L[ℝ] Mid) (Zan Zbn : Lo →L[ℝ] Lo) (Zah Zbh : Hi →L[ℝ] Hi)
    (hGa : I0.comp Gah=Ga.comp I1) (hGb : I0.comp Gbh=Gb.comp I1)
    (hZa : I0.comp Za=Zan.comp I0) (hZb : I0.comp Zb=Zbn.comp I0)
    (hZah : I1.comp Zah=Za.comp I1) (hZbh : I1.comp Zbh=Zb.comp I1)
    (C a b r : ℝ) (hC : 0 ≤ C) (ha : 0 ≤ a) (hb : 0 ≤ b) (hr : 0 ≤ r) (hI : ‖I1‖ ≤ 1)
    (hGaN : ‖Gah‖ ≤ C*a*r) (hGbN : ‖Gbh‖ ≤ C*b*r)
    (hZaN : ‖Zah‖ ≤ C*a*r) (hZbN : ‖Zbh‖ ≤ C*b*r)
    (hZanN : ‖Za‖ ≤ C*a*r) (hZbnN : ‖Zb‖ ≤ C*b*r) :
    GradedHigherEndpointCommutatorBound I0 (Ga+Zan.comp I0) (Gb+Zbn.comp I0)
      (Gah+Za.comp I1) (Gbh+Zb.comp I1) (B+6*C^2*a*b*r^2) := by
  obtain ⟨S,hS,hN⟩ := h
  refine ⟨S+boundedRemainderCommutatorL I1 Gah Gbh Zah Zbh Za Zb,?_,?_⟩
  · exact graded_higher_commutator_bounded_from_graph I1 I0 Ga Gb Gah Gbh S Za Zb Zan Zbn Zah Zbh
      hS hGa hGb hZa hZb hZah hZbh
  · exact (norm_add_le _ _).trans (add_le_add hN
      (norm_boundedRemainderCommutatorL_of_linear_radius I1 Gah Gbh Zah Zbh Za Zb C a b r hC ha hb hr hI
        hGaN hGbN hZaN hZbN hZanN hZbnN))
lemma GradedHigherEndpointCommutatorBound.factor_radius_bound
    {I0 : Mid →L[ℝ] Lo} {Ga Gb : Mid →L[ℝ] Lo} {Gah Gbh : Hi →L[ℝ] Mid}
    {D C a b r : ℝ}
    (h : GradedHigherEndpointCommutatorBound I0 Ga Gb Gah Gbh
      (D*a*b*r^2+6*C^2*a*b*r^2)) :
    GradedHigherEndpointCommutatorBound I0 Ga Gb Gah Gbh ((D+6*C^2)*a*b*r^2) := by
  exact h.mono (le_of_eq (by ring))
end ShrinkingSpheres
