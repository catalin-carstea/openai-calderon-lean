import Proof.CoarseDegreeKernelStructureComparison
import Proof.Archive.ProdInheritedStructureData
import Proof.Archive.PiInheritedStructureData
import Proof.Archive.InheritedNormedStructureData
import Proof.Archive.ClmInheritedStructureData
import Proof.Archive.LpInheritedStructureData
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
open OAI.AnisotropicCalderon.SphereHarmonic OAI.AnisotropicCalderon.ClosedScalarCompatibility OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
 

def coarseDegreeRestrictionCoeNormalizedCache
    {X I : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] := id (by
  have hValue := scalarCompatibilityRestriction_coe_of_mem
    (E := CoarseDegreeData) (X := X) (I := I)
  try simp only [CoarseDegreeData,
      real_nontriviallyNormedField_normedField_eq,
      prod_normedAddCommGroup_seminormedAddCommGroup_eq,
      prod_seminormedAddCommGroup_addCommMonoid_eq,
      prod_normedSpace_module_eq,
      prod_seminormedAddCommGroup_topologicalSpace_eq,
      pi_normedAddCommGroup_seminormedAddCommGroup_eq,
      pi_seminormedAddCommGroup_addCommMonoid_eq,
      pi_normedSpace_module_eq,
      pi_seminormedAddCommGroup_topologicalSpace_eq,
      submodule_normedAddCommGroup_seminormedAddCommGroup_eq,
      clm_normedAddCommGroup_seminormedAddCommGroup_eq,
      normedAddCommGroup_ofSeparation_eq,
      submodule_seminormedAddCommGroup_topologicalSpace_eq,
      submodule_seminormedAddCommGroup_addCommMonoid_eq,
      submodule_normedSpace_module_eq,
      lp_normedAddCommGroup_addCommMonoid_eq,
      lp_normedSpace_module_eq,
      clm_seminormedAddCommGroup_topologicalSpace_eq,
      clm_seminormedAddCommGroup_addCommMonoid_eq,
      clm_normedSpace_module_eq] at hValue
  exact hValue)

def coarseDegreeRestrictionSmoothnessNormalizedCache
    {X I : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] := id (by
  have hSmooth := contDiffOn_scalarCompatibilityRestriction
    (E := CoarseDegreeData) (X := X) (I := I)
  try simp only [CoarseDegreeData,
      real_nontriviallyNormedField_normedField_eq,
      prod_normedAddCommGroup_seminormedAddCommGroup_eq,
      prod_seminormedAddCommGroup_addCommMonoid_eq,
      prod_normedSpace_module_eq,
      prod_seminormedAddCommGroup_topologicalSpace_eq,
      pi_normedAddCommGroup_seminormedAddCommGroup_eq,
      pi_seminormedAddCommGroup_addCommMonoid_eq,
      pi_normedSpace_module_eq,
      pi_seminormedAddCommGroup_topologicalSpace_eq,
      submodule_normedAddCommGroup_seminormedAddCommGroup_eq,
      clm_normedAddCommGroup_seminormedAddCommGroup_eq,
      normedAddCommGroup_ofSeparation_eq,
      submodule_seminormedAddCommGroup_topologicalSpace_eq,
      submodule_seminormedAddCommGroup_addCommMonoid_eq,
      submodule_normedSpace_module_eq,
      lp_normedAddCommGroup_addCommMonoid_eq,
      lp_normedSpace_module_eq,
      clm_seminormedAddCommGroup_topologicalSpace_eq,
      clm_seminormedAddCommGroup_addCommMonoid_eq,
      clm_normedSpace_module_eq] at hSmooth
  exact hSmooth)

end ShrinkingSpheres.CoarseDegreeCompatibility
