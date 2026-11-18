import Proof.CoarseDegreeHalfExtractor
import Proof.CoarseDegreeSmoothRestriction
import Proof.Archive.LinearIsometryTaylorReflection

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxHeartbeats 100000
open Set Filter
open scoped ContDiff Topology InnerProductSpace
namespace ShrinkingSpheres.CoarseDegreeCompatibility
open OAI.AnisotropicCalderon.SphereHarmonic
open OAI.AnisotropicCalderon.ClosedScalarCompatibility
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def subtypeIsometry : compatibleData →ₗᵢ[ℝ] CoarseDegreeData where
  toFun := fun x => x.1
  map_add' := fun _ _ => rfl
  map_smul' := fun _ _ => rfl
  norm_map' := fun _ => rfl

abbrev restriction := @coarseDegreeRestriction

abbrev halfFamily (f : E → CoarseDegreeData) (V : Set E)
    (hOriginal : ∀ x ∈ V,∀ z,constraintL z (f x) = 0) :=
  halfExtractorL ∘ restriction f V hOriginal

lemma contDiffOn_halfFamily (f : E → CoarseDegreeData) (V : Set E) (hV : IsOpen V)
    (hOriginal : ∀ x ∈ V,∀ z,constraintL z (f x) = 0) (hf : ContDiffOn ℝ ∞ f V) :
    ContDiffOn ℝ ∞ (halfFamily f V hOriginal) V :=
  ContDiff.comp_contDiffOn halfExtractorL.contDiff
    (contDiffOn_coarseDegreeRestriction f V hV hOriginal hf)

lemma norm_iteratedFDeriv_restriction (f : E → CoarseDegreeData) (V : Set E) (hV : IsOpen V)
    (hOriginal : ∀ x ∈ V,∀ z,constraintL z (f x) = 0)
    (hf : ContDiffOn ℝ ∞ f V) (x : E) (hx : x ∈ V) (n : ℕ) :
    ‖iteratedFDeriv ℝ n (restriction f V hOriginal) x‖ = ‖iteratedFDeriv ℝ n f x‖ := by
  let R := restriction f V hOriginal
  have hR : ContDiffAt ℝ ∞ R x :=
    (contDiffOn_coarseDegreeRestriction f V hV hOriginal hf).contDiffAt (hV.mem_nhds hx)
  have hGerm : (subtypeIsometry ∘ R) =ᶠ[𝓝 x] f := by
    filter_upwards [hV.mem_nhds hx] with y hy
    exact coarseDegreeRestriction_coe_of_mem f V hOriginal y hy
  exact (subtypeIsometry.norm_iteratedFDeriv_comp_left hR (i:=n) (by simp)).symm.trans
    (congrArg norm ((hGerm.iteratedFDeriv ℝ n).eq_of_nhds))

/-- The coarse graph criterion is linear and retains every parameter
    derivative estimate, with one fixed absolute extraction constant. -/
theorem norm_iteratedFDeriv_halfFamily_le (f : E → CoarseDegreeData) (V : Set E) (hV : IsOpen V)
    (hOriginal : ∀ x ∈ V,∀ z,constraintL z (f x) = 0)
    (hf : ContDiffOn ℝ ∞ f V) (x : E) (hx : x ∈ V)
    (B : ℝ) (hB : 0 ≤ B) (n : ℕ) (hJet : ‖iteratedFDeriv ℝ n f x‖ ≤ B) :
    ‖iteratedFDeriv ℝ n (halfFamily f V hOriginal) x‖ ≤ (12*Real.sqrt 2)*B := by
  let R := restriction f V hOriginal
  have hR : ContDiffAt ℝ ∞ R x :=
    (contDiffOn_coarseDegreeRestriction f V hV hOriginal hf).contDiffAt (hV.mem_nhds hx)
  have hRN : ‖iteratedFDeriv ℝ n R x‖ ≤ B :=
    (norm_iteratedFDeriv_restriction f V hV hOriginal hf x hx n).le.trans hJet
  change ‖iteratedFDeriv ℝ n (halfExtractorL ∘ R) x‖ ≤ _
  rw [halfExtractorL.iteratedFDeriv_comp_left hR (i:=n) (by simp)]
  apply ContinuousMultilinearMap.opNorm_le_bound (by positivity)
  intro v
  change ‖halfExtension (iteratedFDeriv ℝ n R x v)‖ ≤ ((12*Real.sqrt 2)*B)*(∏ i,‖v i‖)
  exact (norm_halfExtension_le _).trans
    ((mul_le_mul_of_nonneg_left
      (((iteratedFDeriv ℝ n R x).le_opNorm v).trans
        (mul_le_mul_of_nonneg_right hRN (Finset.prod_nonneg (fun _ _ => norm_nonneg _))))
      (by positivity : 0 ≤ 12*Real.sqrt 2)).trans_eq (by ring))

lemma halfExtractorL_physical_block (x : compatibleData) (m n : ℕ) (z : harmonicSphereSubspace n) :
    sphereSobolevCoefficientL (-(1/2:ℝ)) m (halfExtractorL x (sphereSobolevSingleL (1/2:ℝ) n z)) =
      ((m:ℝ)-(n:ℝ)) • coarsePhysicalHarmonicBlock x.1.1 m n z := by
  apply ext_inner_right ℝ
  intro w
  have h := halfExtension_pair x (sphereSobolevSingleL 2 n z) (sphereSobolevSingleL 1 m w)
  simp only [sphereSobolevInclusionL_single,sphereSobolevDualPairing_single_left_physical] at h
  exact h.trans (congrArg (fun a : harmonicSphereSubspace m => ⟪a,w⟫_ℝ)
    (coarseDegreeCommutator_physical_block x.1.1 m n z))

end ShrinkingSpheres.CoarseDegreeCompatibility
