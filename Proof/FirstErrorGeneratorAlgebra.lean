import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Tactic.Module
noncomputable section
set_option autoImplicit false
namespace ShrinkingSpheres

/-- Collect the common Taylor generator once. The remaining unbounded terms
are the fixed degree and rotation contribution; the radial correction is bounded. -/
lemma first_error_generator_algebra
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (P D B T : E →L[ℝ] F) (N NC : E →L[ℝ] E) (r α b : ℝ) :
    α • (P.comp N)+b • P+α • (T+(P+D+r • B).comp NC)=
      P.comp (α • N+b • ContinuousLinearMap.id ℝ E+α • NC)+
        α • (T+D.comp NC)+(α*r) • B.comp NC := by
  simp only [ContinuousLinearMap.comp_add,ContinuousLinearMap.add_comp,
    ContinuousLinearMap.comp_smul,ContinuousLinearMap.smul_comp,ContinuousLinearMap.comp_id]
  module
end ShrinkingSpheres
