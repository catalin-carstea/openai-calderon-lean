import Proof.GradedEndpointCommutatorBound
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace ShrinkingSpheres
variable {Hi Mid Lo : Type*} [NormedAddCommGroup Hi] [NormedSpace ℝ Hi]
  [NormedAddCommGroup Mid] [NormedSpace ℝ Mid] [NormedAddCommGroup Lo] [NormedSpace ℝ Lo]

/-- Corrections with ONE radius gain suffice for a quadratic gained
commutator. This reuses the existing six-term bound with rescaled directions. -/
lemma norm_boundedRemainderCommutatorL_of_linear_radius
    (I0 : Mid →L[ℝ] Lo) (Ga Gb : Mid →L[ℝ] Lo)
    (Za Zb : Mid →L[ℝ] Mid) (Zan Zbn : Lo →L[ℝ] Lo)
    (C a b r : ℝ) (hC : 0 ≤ C) (ha : 0 ≤ a) (hb : 0 ≤ b) (hr : 0 ≤ r)
    (hI : ‖I0‖ ≤ 1) (hGa : ‖Ga‖ ≤ C*a*r) (hGb : ‖Gb‖ ≤ C*b*r)
    (hZa : ‖Za‖ ≤ C*a*r) (hZb : ‖Zb‖ ≤ C*b*r)
    (hZan : ‖Zan‖ ≤ C*a*r) (hZbn : ‖Zbn‖ ≤ C*b*r) :
    ‖boundedRemainderCommutatorL I0 Ga Gb Za Zb Zan Zbn‖ ≤ 6*C^2*a*b*r^2 := by
  have hh := norm_boundedRemainderCommutatorL_of_radius I0 Ga Gb Za Zb Zan Zbn
    C (a*r) (b*r) 1 hC (mul_nonneg ha hr) (mul_nonneg hb hr) zero_le_one le_rfl hI
    (by simpa only [mul_one,mul_assoc] using hGa)
    (by simpa only [mul_one,mul_assoc] using hGb)
    (by simpa only [one_pow,mul_one,mul_assoc] using hZa)
    (by simpa only [one_pow,mul_one,mul_assoc] using hZb)
    (by simpa only [one_pow,mul_one,mul_assoc] using hZan)
    (by simpa only [one_pow,mul_one,mul_assoc] using hZbn)
  exact hh.trans_eq (by ring)

lemma GradedEndpointCommutatorBound.add_bounded_linear
    {I : Hi →L[ℝ] Mid} (I0 : Mid →L[ℝ] Lo)
    {Ga Gb : Mid →L[ℝ] Lo} {Gah Gbh : Hi →L[ℝ] Mid} {B : ℝ}
    (h : GradedEndpointCommutatorBound I Ga Gb Gah Gbh B)
    (Za Zb : Mid →L[ℝ] Mid) (Zan Zbn : Lo →L[ℝ] Lo)
    (hGa : I0.comp Gah=Ga.comp I) (hGb : I0.comp Gbh=Gb.comp I)
    (C a b r : ℝ) (hC : 0 ≤ C) (ha : 0 ≤ a) (hb : 0 ≤ b) (hr : 0 ≤ r)
    (hI : ‖I0‖ ≤ 1) (hGaN : ‖Ga‖ ≤ C*a*r) (hGbN : ‖Gb‖ ≤ C*b*r)
    (hZa : ‖Za‖ ≤ C*a*r) (hZb : ‖Zb‖ ≤ C*b*r)
    (hZan : ‖Zan‖ ≤ C*a*r) (hZbn : ‖Zbn‖ ≤ C*b*r) :
    GradedEndpointCommutatorBound I (Ga+Zan.comp I0) (Gb+Zbn.comp I0)
      (Gah+Za.comp I) (Gbh+Zb.comp I) (B+6*C^2*a*b*r^2) := by
  obtain ⟨S,hS,hSN⟩ := h
  refine ⟨S+boundedRemainderCommutatorL I0 Ga Gb Za Zb Zan Zbn,
    graded_commutator_add_bounded_remainders I I0 Ga Gb S Gah Gbh Za Zb Zan Zbn hS hGa hGb,?_⟩
  exact (norm_add_le _ _).trans (add_le_add hSN
    (norm_boundedRemainderCommutatorL_of_linear_radius I0 Ga Gb Za Zb Zan Zbn C a b r hC ha hb hr hI
      hGaN hGbN hZa hZb hZan hZbn))
end ShrinkingSpheres
