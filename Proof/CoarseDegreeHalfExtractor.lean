import Proof.CoarseDegreeNormedStructure
import Proof.Archive.SphereSobolevCompatibleEndpointInterpolation
import Proof.CoarseDegreeLinearity
import Proof.CoarseHalfDualUniqueness

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set
open scoped InnerProductSpace ContDiff
namespace ShrinkingSpheres.CoarseDegreeCompatibility
open OAI.AnisotropicCalderon.SphereHarmonic
open OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

lemma exists_compatible_half_operator (x : compatibleData) :
    ∃ S : SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ)),
      ‖S‖ ≤ (12*Real.sqrt 2)*‖x‖ ∧
      ∀ u v,sphereSobolevDualPairing (1/2:ℝ)
        (sphereSobolevInclusionL 1 (1/2:ℝ) (by norm_num) v)
        (S (sphereSobolevInclusionL 2 (1/2:ℝ) (by norm_num) u)) =
          sphereSobolevDualPairing 1 v (coarseDegreeCommutator x.1.1 u) := by
  have hP (ij : I × I) : ‖x.1.2.1 ij‖ ≤ ‖x‖ :=
    (norm_le_pi_norm x.1.2.1 ij).trans ((norm_fst_le x.1.2).trans (norm_snd_le x.1))
  have hQ (ij : I × I) : ‖x.1.2.2 ij‖ ≤ ‖x‖ :=
    (norm_le_pi_norm x.1.2.2 ij).trans ((norm_snd_le x.1.2).trans (norm_snd_le x.1))
  have hMem := (mem_compatibleData_iff x.1).mp x.2
  obtain ⟨S,hS,hPair,_⟩ := exists_half_degree_commutator_of_coarse_rotation_blocks
    x.1.1 x.1.2.1 x.1.2.2 ‖x‖ ‖x‖ (norm_nonneg x) (norm_nonneg x) hP hQ hMem.2 hMem.1
  refine ⟨S,hS.trans_eq ?_,hPair⟩
  ring

def halfExtension (x : compatibleData) :
    SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ)) :=
  Classical.choose (exists_compatible_half_operator x)

lemma norm_halfExtension_le (x : compatibleData) :
    ‖halfExtension x‖ ≤ (12*Real.sqrt 2)*‖x‖ :=
  (Classical.choose_spec (exists_compatible_half_operator x)).1

lemma halfExtension_pair (x : compatibleData) (u : SphereSobolev 2) (v : SphereSobolev 1) :
    sphereSobolevDualPairing (1/2:ℝ)
      (sphereSobolevInclusionL 1 (1/2:ℝ) (by norm_num) v)
      (halfExtension x (sphereSobolevInclusionL 2 (1/2:ℝ) (by norm_num) u)) =
        sphereSobolevDualPairing 1 v (coarseDegreeCommutator x.1.1 u) :=
  (Classical.choose_spec (exists_compatible_half_operator x)).2 u v

lemma halfExtension_add (x y : compatibleData) :
    halfExtension (x+y) = halfExtension x+halfExtension y := by
  apply half_operator_eq_of_coarse_dual_pairs
  intro u v
  rw [halfExtension_pair]
  have hRaw : coarseDegreeCommutator (x+y).1.1 =
      coarseDegreeCommutator x.1.1+coarseDegreeCommutator y.1.1 :=
    coarseDegreeCommutator_add x.1.1 y.1.1
  rw [hRaw]
  change ⟪v,coarseDegreeCommutator x.1.1 u+coarseDegreeCommutator y.1.1 u⟫_ℝ =
    ⟪sphereSobolevInclusionL 1 (1/2:ℝ) (by norm_num) v,
      halfExtension x (sphereSobolevInclusionL 2 (1/2:ℝ) (by norm_num) u)+
      halfExtension y (sphereSobolevInclusionL 2 (1/2:ℝ) (by norm_num) u)⟫_ℝ
  calc
    _ = ⟪v,coarseDegreeCommutator x.1.1 u⟫_ℝ+⟪v,coarseDegreeCommutator y.1.1 u⟫_ℝ :=
      inner_add_right _ _ _
    _ = _ := congrArg₂ (fun a b : ℝ => a+b) (halfExtension_pair x u v).symm (halfExtension_pair y u v).symm
    _ = _ := (inner_add_right _ _ _).symm

lemma halfExtension_smul (c : ℝ) (x : compatibleData) :
    halfExtension (c • x) = c • halfExtension x := by
  apply half_operator_eq_of_coarse_dual_pairs
  intro u v
  rw [halfExtension_pair]
  have hRaw : coarseDegreeCommutator (c • x).1.1 = c • coarseDegreeCommutator x.1.1 :=
    coarseDegreeCommutator_smul c x.1.1
  rw [hRaw]
  change ⟪v,c • coarseDegreeCommutator x.1.1 u⟫_ℝ =
    ⟪sphereSobolevInclusionL 1 (1/2:ℝ) (by norm_num) v,
      c • halfExtension x (sphereSobolevInclusionL 2 (1/2:ℝ) (by norm_num) u)⟫_ℝ
  calc
    _ = c*⟪v,coarseDegreeCommutator x.1.1 u⟫_ℝ := inner_smul_right _ _ _
    _ = _ := congrArg (fun a : ℝ => c*a) (halfExtension_pair x u v).symm
    _ = _ := (inner_smul_right _ _ _).symm

/-- A fixed continuous linear extractor gives the degree commutator for
    compatible coarse rotation/adjoint data, including every parameter jet. -/
local instance halfExtractorOperatorNorm
    :
    Norm (compatibleData →L[ℝ]
      (SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ)))) := by
  have hNorm := ContinuousLinearMap.hasOpNorm
    (E := compatibleData)
    (F := SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ)))
    (σ₁₂ := RingHom.id ℝ)
  simpa only [compatibleData_topologicalSpace_eq,
    compatibleData_addCommMonoid_eq_standard,
    compatibleData_module_eq_standard,
    real_nontriviallyNormedField_normedField_eq,
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
    clm_normedSpace_module_eq] using hNorm

def halfExtractorL
    :
    compatibleData →L[ℝ]
      (SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ))) := by
  let A : compatibleData →ₗ[ℝ]
      (SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ))) :=
    { toFun := halfExtension
      map_add' := halfExtension_add
      map_smul' := halfExtension_smul }
  have hConstructor := sphereInterpolationBoundedLinearMap
    (X := compatibleData)
    (Y := SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ)))
  try simp only [compatibleData_topologicalSpace_eq,
    compatibleData_addCommMonoid_eq_standard,
    compatibleData_module_eq_standard,
    real_nontriviallyNormedField_normedField_eq,
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
    clm_normedSpace_module_eq] at hConstructor
  exact hConstructor A (12*Real.sqrt 2) (norm_halfExtension_le)

lemma halfExtractorL_apply
    (x : compatibleData) :
    halfExtractorL x = halfExtension x := rfl

lemma norm_halfExtractorL_le
    :
    ‖halfExtractorL‖ ≤ 12*Real.sqrt 2 := by
  have hBound := ContinuousLinearMap.opNorm_le_bound
    (E := compatibleData)
    (F := SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ)))
    (σ₁₂ := RingHom.id ℝ)
  try simp only [compatibleData_topologicalSpace_eq,
    compatibleData_addCommMonoid_eq_standard,
    compatibleData_module_eq_standard,
    real_nontriviallyNormedField_normedField_eq,
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
    clm_normedSpace_module_eq] at hBound
  apply hBound (halfExtractorL) (by positivity)
  intro x
  change ‖halfExtension x‖ ≤ (12*Real.sqrt 2)*‖x‖
  exact norm_halfExtension_le x


end ShrinkingSpheres.CoarseDegreeCompatibility
