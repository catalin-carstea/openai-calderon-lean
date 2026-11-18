import Proof.CoarseDegreeNormalizedRestrictionCache
import Proof.CoarseDegreeKernelSmoothnessTransportCache
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
 


def coarseDegreeScalarRestrictionCoeCache
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    := id (by
  have hValue := coarseDegreeRestrictionCoeNormalizedCache (X := X) (I := ConstraintIndex)
  have hActualValue := hValue (constraintL)
  exact hActualValue)

def coarseDegreeScalarRestrictionSmoothness
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (f : X → CoarseDegreeData) (s : Set X) (hs : IsOpen s)
    (hOriginal : ∀ x ∈ s, ∀ z, constraintL z (f x) = 0)
    (hf : ContDiffOn ℝ ∞ f s) := id (by
  have hTransport := coarseDegreeKernelSmoothnessTransportCache (X := X)
  have hSmooth := coarseDegreeRestrictionSmoothnessNormalizedCache (X := X) (I := ConstraintIndex)
  have hF := hf
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
      clm_normedSpace_module_eq] at hF
  have hStandard := hSmooth (constraintL) f s hs hOriginal hF
  have hActual := hTransport _ _ hStandard
  exact hActual)

end ShrinkingSpheres.CoarseDegreeCompatibility
