import Proof.GradedBoundedRemainderAlgebra
import Proof.GradedFiniteGeneratorCommutator
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
namespace ShrinkingSpheres
variable {Hi Mid Lo : Type*} [NormedAddCommGroup Hi] [NormedSpace ℝ Hi]
  [NormedAddCommGroup Mid] [NormedSpace ℝ Mid] [NormedAddCommGroup Lo] [NormedSpace ℝ Lo]

def boundedRemainderCommutatorL (I0 : Mid →L[ℝ] Lo)
    (Ga Gb : Mid →L[ℝ] Lo) (Za Zb : Mid →L[ℝ] Mid) (Zan Zbn : Lo →L[ℝ] Lo) : Mid →L[ℝ] Lo :=
  Ga.comp Zb-Gb.comp Za+Zan.comp Gb-Zbn.comp Ga+
    Zan.comp (I0.comp Zb)-Zbn.comp (I0.comp Za)

/-- Adding compatible bounded remainders preserves the first-order graph
of a commutator. The principal generator estimate is reused unchanged. -/
lemma graded_commutator_add_bounded_remainders
    (I : Hi →L[ℝ] Mid) (I0 : Mid →L[ℝ] Lo)
    (Ga Gb K : Mid →L[ℝ] Lo) (Gah Gbh : Hi →L[ℝ] Mid)
    (Za Zb : Mid →L[ℝ] Mid) (Zan Zbn : Lo →L[ℝ] Lo)
    (hK : Ga.comp Gbh-Gb.comp Gah=K.comp I)
    (hGa : I0.comp Gah=Ga.comp I) (hGb : I0.comp Gbh=Gb.comp I) :
    (Ga+Zan.comp I0).comp (Gbh+Zb.comp I)-
      (Gb+Zbn.comp I0).comp (Gah+Za.comp I)=
    (K+boundedRemainderCommutatorL I0 Ga Gb Za Zb Zan Zbn).comp I := by
  have hExpand := graded_bounded_remainder_expansion I I0 Ga Gb Gah Gbh Za Zb Zan Zbn hGa hGb
  have hEq : (Ga.comp Gbh-Gb.comp Gah)+(boundedRemainderCommutatorL I0 Ga Gb Za Zb Zan Zbn).comp I=
      (K+boundedRemainderCommutatorL I0 Ga Gb Za Zb Zan Zbn).comp I := by
    rw [hK,ContinuousLinearMap.add_comp]
  exact hExpand.trans hEq

lemma norm_boundedRemainderCommutatorL_le (I0 : Mid →L[ℝ] Lo)
    (Ga Gb : Mid →L[ℝ] Lo) (Za Zb : Mid →L[ℝ] Mid) (Zan Zbn : Lo →L[ℝ] Lo) :
    ‖boundedRemainderCommutatorL I0 Ga Gb Za Zb Zan Zbn‖ ≤
      ‖Ga‖*‖Zb‖+‖Gb‖*‖Za‖+‖Zan‖*‖Gb‖+‖Zbn‖*‖Ga‖+
      ‖Zan‖*(‖I0‖*‖Zb‖)+‖Zbn‖*(‖I0‖*‖Za‖) := by
  have h1 := norm_sub_le (Ga.comp Zb) (Gb.comp Za)
  have h2 := norm_add_le (Ga.comp Zb-Gb.comp Za) (Zan.comp Gb)
  have h3 := norm_sub_le (Ga.comp Zb-Gb.comp Za+Zan.comp Gb) (Zbn.comp Ga)
  have h4 := norm_add_le (Ga.comp Zb-Gb.comp Za+Zan.comp Gb-Zbn.comp Ga) (Zan.comp (I0.comp Zb))
  have h5 := norm_sub_le (Ga.comp Zb-Gb.comp Za+Zan.comp Gb-Zbn.comp Ga+Zan.comp (I0.comp Zb))
    (Zbn.comp (I0.comp Za))
  have h6 := (Zan.opNorm_comp_le (I0.comp Zb)).trans
    (mul_le_mul_of_nonneg_left (I0.opNorm_comp_le Zb) (norm_nonneg Zan))
  have h7 := (Zbn.opNorm_comp_le (I0.comp Za)).trans
    (mul_le_mul_of_nonneg_left (I0.opNorm_comp_le Za) (norm_nonneg Zbn))
  dsimp only [boundedRemainderCommutatorL]
  linarith only [h1,h2,h3,h4,h5,h6,h7,Ga.opNorm_comp_le Zb,Gb.opNorm_comp_le Za,
    Zan.opNorm_comp_le Gb,Zbn.opNorm_comp_le Ga]
end ShrinkingSpheres
