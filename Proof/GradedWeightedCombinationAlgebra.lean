import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
noncomputable section
set_option autoImplicit false
namespace ShrinkingSpheres
variable {Hi Mid Lo : Type*} [NormedAddCommGroup Hi] [NormedSpace ℝ Hi]
  [NormedAddCommGroup Mid] [NormedSpace ℝ Mid] [NormedAddCommGroup Lo] [NormedSpace ℝ Lo]

/-- Shared exact expansion for real weighted families on graded domains. -/
lemma finite_real_combination_commutator_expansion {ι κ : Type*} [Fintype ι] [Fintype κ]
    (Ga : ι → Mid →L[ℝ] Lo) (Gb : κ → Mid →L[ℝ] Lo)
    (Gah : ι → Hi →L[ℝ] Mid) (Gbh : κ → Hi →L[ℝ] Mid) (u : ι → ℝ) (v : κ → ℝ) :
    (∑ i,u i • Ga i).comp (∑ j,v j • Gbh j)-
      (∑ j,v j • Gb j).comp (∑ i,u i • Gah i)=
    ∑ i,∑ j,(u i*v j) • ((Ga i).comp (Gbh j)-(Gb j).comp (Gah i)) := by
  classical
  have hForward : (∑ i,u i • Ga i).comp (∑ j,v j • Gbh j)=
      ∑ i,∑ j,(u i*v j) • (Ga i).comp (Gbh j) := by
    apply ContinuousLinearMap.ext
    intro x
    simp only [_root_.sum_apply,ContinuousLinearMap.comp_apply,_root_.smul_apply,map_sum,map_smul,
      Finset.smul_sum,smul_smul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [mul_comm]
  have hReverse : (∑ j,v j • Gb j).comp (∑ i,u i • Gah i)=
      ∑ i,∑ j,(u i*v j) • (Gb j).comp (Gah i) := by
    apply ContinuousLinearMap.ext
    intro x
    simp only [_root_.sum_apply,ContinuousLinearMap.comp_apply,_root_.smul_apply,map_sum,map_smul,
      Finset.smul_sum,smul_smul]
  rw [hForward,hReverse]
  simp only [smul_sub,Finset.sum_sub_distrib]
end ShrinkingSpheres
