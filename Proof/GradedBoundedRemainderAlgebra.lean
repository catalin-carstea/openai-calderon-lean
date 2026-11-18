import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Tactic.Abel
noncomputable section
set_option autoImplicit false
namespace ShrinkingSpheres
variable {Hi Mid Lo : Type*} [NormedAddCommGroup Hi] [NormedSpace ℝ Hi]
  [NormedAddCommGroup Mid] [NormedSpace ℝ Mid] [NormedAddCommGroup Lo] [NormedSpace ℝ Lo]

/-- The common six-word expansion before choosing a lower or higher
    realization of the principal commutator. -/
lemma graded_bounded_remainder_expansion
    (I : Hi →L[ℝ] Mid) (I0 : Mid →L[ℝ] Lo)
    (Ga Gb : Mid →L[ℝ] Lo) (Gah Gbh : Hi →L[ℝ] Mid)
    (Za Zb : Mid →L[ℝ] Mid) (Zan Zbn : Lo →L[ℝ] Lo)
    (hGa : I0.comp Gah=Ga.comp I) (hGb : I0.comp Gbh=Gb.comp I) :
    (Ga+Zan.comp I0).comp (Gbh+Zb.comp I)-(Gb+Zbn.comp I0).comp (Gah+Za.comp I)=
      (Ga.comp Gbh-Gb.comp Gah)+
      (Ga.comp Zb-Gb.comp Za+Zan.comp Gb-Zbn.comp Ga+
        Zan.comp (I0.comp Zb)-Zbn.comp (I0.comp Za)).comp I := by
  have hZan := congrArg (fun T : Hi →L[ℝ] Lo => Zan.comp T) hGb
  have hZbn := congrArg (fun T : Hi →L[ℝ] Lo => Zbn.comp T) hGa
  simp only [ContinuousLinearMap.add_comp,ContinuousLinearMap.comp_add,ContinuousLinearMap.sub_comp,
    ContinuousLinearMap.comp_assoc]
  rw [hZan,hZbn]
  abel
end ShrinkingSpheres
