import Proof.NativeTaylorScalarCombination
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace ShrinkingSpheres
variable {κ V E F : Type*} [Fintype κ]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Canonical continuous-linear dependence of a finite right scalar
generator combination on its shared scalar coefficient family. -/
def rightScalarCombinationL (G : κ → E →L[ℝ] F) (M : V →L[ℝ] (E →L[ℝ] E)) :
    (κ → V) →L[ℝ] (E →L[ℝ] F) :=
  ∑ a,((ContinuousLinearMap.compL ℝ E E F) (G a)).comp (M.comp (ContinuousLinearMap.proj a))

lemma rightScalarCombinationL_apply (G : κ → E →L[ℝ] F) (M : V →L[ℝ] (E →L[ℝ] E)) (Q : κ → V) :
    rightScalarCombinationL G M Q=∑ a,(G a).comp (M (Q a)) := by
  simp only [rightScalarCombinationL,_root_.sum_apply,ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.proj_apply,ContinuousLinearMap.compL_apply]
end ShrinkingSpheres
