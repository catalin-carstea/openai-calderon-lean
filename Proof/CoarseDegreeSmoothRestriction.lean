import Proof.CoarseDegreeSmoothRestrictionCore
import Proof.CoarseDegreeScalarRestrictionSpecialization
import Proof.CoarseDegreeCompatibility
import Proof.Archive.ClosedScalarCompatibilityQuotient
import Proof.Archive.ProdInheritedStructureData
import Proof.Archive.PiInheritedStructureData
import Proof.Archive.InheritedNormedStructureData
import Proof.Archive.ClmInheritedStructureData
import Proof.Archive.LpInheritedStructureData
import Proof.CoarseDegreeNormedStructure
import Proof.CoarseDegreeCanonicalStructureComparison
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
open OAI.AnisotropicCalderon.SphereHarmonic OAI.AnisotropicCalderon.ClosedScalarCompatibility OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
 

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

lemma contDiffOn_coarseDegreeRestriction
    (f : X → CoarseDegreeData) (s : Set X) (hs : IsOpen s)
    (hOriginal : ∀ x ∈ s, ∀ z, constraintL z (f x) = 0)
    (hf : ContDiffOn ℝ ∞ f s) :
    ContDiffOn ℝ ∞ (coarseDegreeRestriction f s hOriginal) s := by
  have hActual := coarseDegreeScalarRestrictionSmoothness f s hs hOriginal hf
  have hValue := coarseDegreeScalarRestrictionCoeCache (X := X)
  apply hActual.congr
  intro x hx
  apply Subtype.ext
  have hStandardValue := hValue f s hOriginal x hx
  exact (coarseDegreeRestriction_coe_of_mem f s hOriginal x hx).trans hStandardValue.symm

end ShrinkingSpheres.CoarseDegreeCompatibility
