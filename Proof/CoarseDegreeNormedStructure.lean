import Proof.CoarseDegreeCompatibility
import Proof.Archive.ProdInheritedStructureData
import Proof.Archive.PiInheritedStructureData
import Proof.Archive.InheritedNormedStructureData
import Proof.Archive.ClmInheritedStructureData
import Proof.Archive.LpInheritedStructureData
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace ShrinkingSpheres.CoarseDegreeCompatibility
open OAI.AnisotropicCalderon.SphereHarmonic OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
 



def coarseDegreeData_smul :
    SMul ℝ CoarseDegreeData :=
  (inferInstance : NormedSpace ℝ CoarseDegreeData).toModule.toSMul

instance (priority := 1100) coarseDegreeData_isScalarTower :
    IsScalarTower ℝ ℝ CoarseDegreeData :=
  IsScalarTower.left (α := CoarseDegreeData) ℝ

instance (priority := 1100) compatibleData_normedAddCommGroup
    :
    NormedAddCommGroup (compatibleData) := by
  have hCanonical := Submodule.normedAddCommGroup (𝕜 := ℝ) (E := CoarseDegreeData)
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
      clm_normedSpace_module_eq] at hCanonical
  simpa only [id_eq, CoarseDegreeData,
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
      clm_normedSpace_module_eq] using
    hCanonical (compatibleData)

instance (priority := 1100) compatibleData_seminormedAddCommGroup
    :
    SeminormedAddCommGroup (compatibleData) :=
  (compatibleData_normedAddCommGroup).toSeminormedAddCommGroup

instance (priority := 1100) compatibleData_norm
    :
    Norm (compatibleData) :=
  (compatibleData_normedAddCommGroup).toNorm

instance (priority := 1100) compatibleData_smul
    :
    SMul ℝ (compatibleData) :=
  Submodule.smul (S := ℝ) (R := ℝ) (M := CoarseDegreeData)
    (compatibleData)

instance (priority := 1100) compatibleData_normedSpace
    :
    NormedSpace ℝ (compatibleData) := by
  have hCanonical := Submodule.normedSpace (𝕜 := ℝ) (R := ℝ) (E := CoarseDegreeData)
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
      clm_normedSpace_module_eq] at hCanonical
  simpa only [id_eq, compatibleData_seminormedAddCommGroup,
      compatibleData_normedAddCommGroup, CoarseDegreeData,
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
      clm_normedSpace_module_eq] using
    hCanonical (compatibleData)

lemma compatibleData_norm_coe
    (x : compatibleData) :
    ‖(x : CoarseDegreeData)‖ = ‖x‖ := by
  rfl

lemma compatibleData_coe_add
    (x y : compatibleData) :
    ((x+y : compatibleData) : CoarseDegreeData) =
      (x : CoarseDegreeData) + (y : CoarseDegreeData) := by
  rfl

lemma compatibleData_coe_smul
    (c : ℝ) (x : compatibleData) :
    ((c • x : compatibleData) : CoarseDegreeData) =
      @SMul.smul ℝ CoarseDegreeData
        coarseDegreeData_smul c (x : CoarseDegreeData) := by
  rfl

lemma compatibleData_topologicalSpace_eq
    :
    (compatibleData_normedAddCommGroup).toMetricSpace.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace =
      (inferInstance : TopologicalSpace (compatibleData)) := by
  rfl

lemma compatibleData_addCommMonoid_eq_standard :
    compatibleData_normedAddCommGroup.toSeminormedAddCommGroup.toAddCommGroup.toAddCommMonoid =
      compatibleData.addCommMonoid := rfl

lemma compatibleData_module_eq_standard :
    compatibleData_normedSpace.toModule = compatibleData.module := rfl

end ShrinkingSpheres.CoarseDegreeCompatibility
