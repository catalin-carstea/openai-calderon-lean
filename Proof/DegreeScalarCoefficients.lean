import Proof.RightScalarCombination
import Proof.FirstErrorScalarCoefficientBounds
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
open scoped ContDiff
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.DirichletFamily OAI.AnisotropicCalderon.SphereHarmonic

def degreeScalarCoefficients (Q0 : SmoothCoefficientJets 2) : TaylorGeneratorIndex → ClosedCoefficientJets 3
  | .degree => closedUnitCoefficient Q0
  | _ => 0

lemma degree_scalar_coefficients_form {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    (G : TaylorGeneratorIndex → E →L[ℝ] F)
    (M : ClosedCoefficientJets 3 →L[ℝ] (E →L[ℝ] E))
    (Q0 : SmoothCoefficientJets 2) (hUnit : M (closedUnitCoefficient Q0)=ContinuousLinearMap.id ℝ E) :
    rightScalarCombinationL G M (degreeScalarCoefficients Q0)=G .degree := by
  rw [rightScalarCombinationL_apply,taylorGeneratorIndex_sum]
  simp only [degreeScalarCoefficients,M.map_zero,ContinuousLinearMap.comp_zero,zero_add,hUnit,
    ContinuousLinearMap.comp_id,Finset.sum_const_zero,add_zero]

lemma degreeScalarCoefficients_weighted_bound (Q0 : SmoothCoefficientJets 2) (r : ℝ) :
    (∑ a,taylorGeneratorWeight r a*‖degreeScalarCoefficients Q0 a‖) ≤ firstErrorScalarFixedBudget Q0 := by
  rw [taylorGeneratorIndex_sum]
  simpa only [degreeScalarCoefficients,taylorGeneratorWeight,norm_zero,mul_zero,zero_add,one_mul,
    Finset.sum_const_zero,add_zero] using (firstErrorScalarFixedBudget_bounds Q0).2.1
end ShrinkingSpheres
