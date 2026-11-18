import Proof.CoarseDegreeNormedStructure
import Mathlib.Analysis.Calculus.ContDiff.Defs
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option maxSynthPendingDepth 30
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open scoped ContDiff ENNReal
namespace ShrinkingSpheres.CoarseDegreeCompatibility
open OAI.AnisotropicCalderon.SphereHarmonic
 


def coarseDegreeData_module : Module ℝ CoarseDegreeData :=
  (inferInstance : NormedSpace ℝ CoarseDegreeData).toModule

lemma compatibleData_normedAddCommGroup_eq_standard
    :
    compatibleData_normedAddCommGroup =
      @Submodule.normedAddCommGroup ℝ CoarseDegreeData
        (inferInstance : Ring ℝ) (inferInstance : NormedAddCommGroup CoarseDegreeData)
        coarseDegreeData_module (compatibleData) := by
  rfl

lemma compatibleData_normedSpace_heq_standard
    :
    HEq (compatibleData_normedSpace)
      (Submodule.normedSpace (𝕜 := ℝ) (R := ℝ) (E := CoarseDegreeData)
        (compatibleData)) := by
  rfl

lemma contDiffOn_of_heq_codomain_structures
    {𝕜 : Type*} [NontriviallyNormedField 𝕜]
    {X : Type*} [NormedAddCommGroup X] [NormedSpace 𝕜 X]
    {F : Type*} (G₁ G₂ : NormedAddCommGroup F)
    (V₁ : @NormedSpace 𝕜 F (inferInstance : NormedField 𝕜) G₁.toSeminormedAddCommGroup)
    (V₂ : @NormedSpace 𝕜 F (inferInstance : NormedField 𝕜) G₂.toSeminormedAddCommGroup)
    (hG : G₁ = G₂) (hV : HEq V₁ V₂) (f : X → F) (s : Set X)
    (hf : @ContDiffOn 𝕜 (inferInstance : NontriviallyNormedField 𝕜)
      X (inferInstance : NormedAddCommGroup X) (inferInstance : NormedSpace 𝕜 X)
      F G₂ V₂ ∞ f s) :
    @ContDiffOn 𝕜 (inferInstance : NontriviallyNormedField 𝕜)
      X (inferInstance : NormedAddCommGroup X) (inferInstance : NormedSpace 𝕜 X)
      F G₁ V₁ ∞ f s := by
  cases hG
  cases hV
  exact hf

end ShrinkingSpheres.CoarseDegreeCompatibility
