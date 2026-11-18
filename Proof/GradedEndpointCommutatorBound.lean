import Proof.GradedBoundedRemainderRadius
import Proof.TaylorScalarCombinationProperty
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace ShrinkingSpheres
variable {Hi Mid Lo : Type*} [NormedAddCommGroup Hi] [NormedSpace ℝ Hi]
  [NormedAddCommGroup Mid] [NormedSpace ℝ Mid] [NormedAddCommGroup Lo] [NormedSpace ℝ Lo]

def GradedEndpointCommutatorBound (I : Hi →L[ℝ] Mid) (Ga Gb : Mid →L[ℝ] Lo)
    (Gah Gbh : Hi →L[ℝ] Mid) (B : ℝ) : Prop :=
  ∃ S : Mid →L[ℝ] Lo,Ga.comp Gbh-Gb.comp Gah=S.comp I ∧ ‖S‖ ≤ B

lemma GradedEndpointCommutatorBound.mono
    {I : Hi →L[ℝ] Mid} {Ga Gb : Mid →L[ℝ] Lo} {Gah Gbh : Hi →L[ℝ] Mid} {B B' : ℝ}
    (h : GradedEndpointCommutatorBound I Ga Gb Gah Gbh B) (hB : B ≤ B') :
    GradedEndpointCommutatorBound I Ga Gb Gah Gbh B' := by
  obtain ⟨S,hS,hN⟩ := h
  exact ⟨S,hS,hN.trans hB⟩

lemma GradedEndpointCommutatorBound.congr
    {I : Hi →L[ℝ] Mid} {Ga Gb Ga' Gb' : Mid →L[ℝ] Lo}
    {Gah Gbh Gah' Gbh' : Hi →L[ℝ] Mid} {B : ℝ}
    (h : GradedEndpointCommutatorBound I Ga Gb Gah Gbh B)
    (ha : Ga=Ga') (hb : Gb=Gb') (hah : Gah=Gah') (hbh : Gbh=Gbh') :
    GradedEndpointCommutatorBound I Ga' Gb' Gah' Gbh' B := by
  subst Ga';subst Gb';subst Gah';subst Gbh';exact h

lemma GradedEndpointCommutatorBound.add_bounded
    {I : Hi →L[ℝ] Mid} (I0 : Mid →L[ℝ] Lo)
    {Ga Gb : Mid →L[ℝ] Lo} {Gah Gbh : Hi →L[ℝ] Mid} {B : ℝ}
    (h : GradedEndpointCommutatorBound I Ga Gb Gah Gbh B)
    (Za Zb : Mid →L[ℝ] Mid) (Zan Zbn : Lo →L[ℝ] Lo)
    (hGa : I0.comp Gah=Ga.comp I) (hGb : I0.comp Gbh=Gb.comp I)
    (C a b r : ℝ) (hC : 0 ≤ C) (ha : 0 ≤ a) (hb : 0 ≤ b) (hr : 0 ≤ r) (hr1 : r ≤ 1)
    (hI : ‖I0‖ ≤ 1) (hGaN : ‖Ga‖ ≤ C*a*r) (hGbN : ‖Gb‖ ≤ C*b*r)
    (hZa : ‖Za‖ ≤ C*a*r^2) (hZb : ‖Zb‖ ≤ C*b*r^2)
    (hZan : ‖Zan‖ ≤ C*a*r^2) (hZbn : ‖Zbn‖ ≤ C*b*r^2) :
    GradedEndpointCommutatorBound I (Ga+Zan.comp I0) (Gb+Zbn.comp I0)
      (Gah+Za.comp I) (Gbh+Zb.comp I) (B+6*C^2*a*b*r^2) := by
  obtain ⟨S,hS,hSN⟩ := h
  refine ⟨S+boundedRemainderCommutatorL I0 Ga Gb Za Zb Zan Zbn,
    graded_commutator_add_bounded_remainders I I0 Ga Gb S Gah Gbh Za Zb Zan Zbn hS hGa hGb,?_⟩
  exact (norm_add_le _ _).trans (add_le_add hSN
    (norm_boundedRemainderCommutatorL_of_radius I0 Ga Gb Za Zb Zan Zbn C a b r hC ha hb hr hr1 hI hGaN hGbN hZa hZb hZan hZbn))

open OAI.AnisotropicCalderon.DirichletFamily OAI.AnisotropicCalderon.SphereHarmonic
lemma TaylorScalarCombinationCommutes.graded_bound
    {P : SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ))}
    {Ph : SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ)}
    {Q R : TaylorGeneratorIndex → ClosedCoefficientJets 3} {B : ℝ}
    (h : TaylorScalarCombinationCommutes P Ph Q R B) :
    GradedEndpointCommutatorBound (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num))
      (∑ a,(taylorGeneratorLow P a).comp (closedThreeJetHalfBoundaryScalarMultiplierL (Q a)))
      (∑ b,(taylorGeneratorLow P b).comp (closedThreeJetHalfBoundaryScalarMultiplierL (R b)))
      (∑ a,(taylorGeneratorHigh Ph a).comp (closedThreeJetHigherScalarMultiplierL (Q a)))
      (∑ b,(taylorGeneratorHigh Ph b).comp (closedThreeJetHigherScalarMultiplierL (R b))) B := h
end ShrinkingSpheres
