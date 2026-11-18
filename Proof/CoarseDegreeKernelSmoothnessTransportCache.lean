import Proof.CoarseDegreeKernelStructureComparison
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option maxSynthPendingDepth 30
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open Set
open scoped ContDiff ENNReal
namespace ShrinkingSpheres.CoarseDegreeCompatibility
open OAI.AnisotropicCalderon.SphereHarmonic OAI.AnisotropicCalderon.ClosedScalarCompatibility
 


def coarseDegreeKernelSmoothnessTransportCache
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    := id (by
  have hG := compatibleData_normedAddCommGroup_eq_kernel
  have hV := compatibleData_normedSpace_heq_kernel
  have hTransfer := contDiffOn_of_heq_codomain_structures
    (𝕜 := ℝ) (X := X) _ _ _ _ hG hV
  exact hTransfer)

end ShrinkingSpheres.CoarseDegreeCompatibility
