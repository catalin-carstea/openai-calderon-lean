import Proof.CoarseDegreeCanonicalStructureComparison
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option maxSynthPendingDepth 30
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace ShrinkingSpheres.CoarseDegreeCompatibility
open OAI.AnisotropicCalderon.SphereHarmonic OAI.AnisotropicCalderon.ClosedScalarCompatibility
 


lemma compatibleData_normedAddCommGroup_eq_kernel
    :
    compatibleData_normedAddCommGroup =
      @Submodule.normedAddCommGroup ℝ CoarseDegreeData
        (inferInstance : Ring ℝ) (inferInstance : NormedAddCommGroup CoarseDegreeData)
        coarseDegreeData_module
        (simultaneousScalarKernel (constraintL)) := by
  rfl

lemma compatibleData_normedSpace_heq_kernel
    :
    HEq (compatibleData_normedSpace)
      (Submodule.normedSpace (𝕜 := ℝ) (R := ℝ) (E := CoarseDegreeData)
        (simultaneousScalarKernel (constraintL))) := by
  rfl

end ShrinkingSpheres.CoarseDegreeCompatibility
