import Proof.UniformRotatedWeakEnergy
import Proof.OrthogonalAffineCoefficient

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter Function
open scoped ContDiff Topology Matrix.Norms.Elementwise
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.EnergyBridge OAI.AnisotropicCalderon.DirichletFamily
open OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open OAI.AnisotropicCalderon.SmoothSphereRotation
attribute [local instance] TauCeti.W1p0.instNormedAddCommGroup TauCeti.W1p0.instInnerProductSpace

/-- A genuine compact whole-angle first scalar model, with uniform native
    weak energy derivative constants controlled by the actual linear form. -/
theorem exists_rotated_linear_scalar_weakEnergy_family (i j : I) (ell : X →L[ℝ] ℝ) :
    ∃ a : ℝ × X → Mat,∃ ha : ContDiff ℝ ∞ a,∃ S : Set X,∃ hS : IsCompact S,
      ∃ hz : ∀ θ z,z ∉ S → a (θ,z) = 0,
      (∀ θ z,z ∈ Metric.closedBall (0:X) 2 → a (θ,z) = ell (coordinateRotation i j θ z) • (1:Mat)) ∧
      ‖fderiv ℝ (commonSupportFullWeakEnergy a ha) 0‖ ≤ 14*weakFullDerivativeBudget*‖ell‖ ∧
      ‖fderiv ℝ (commonSupportWeakEnergy a ha) 0‖ ≤ 14*weakFullDerivativeBudget*‖ell‖ ∧
      ‖fderiv ℝ (commonSupportZeroWeakEnergy a ha) 0‖ ≤ 14*weakFullDerivativeBudget*‖ell‖ := by
  let R : X → Mat := fun z => ell z • (1:Mat)
  have hR : ContDiff ℝ ∞ R := ell.contDiff.smul contDiff_const
  have hCompactTheorem := exists_contDiff_eq_near_compact_of_contDiffOn
    (Metric.closedBall (0:X) 2) Set.univ (isCompact_closedBall _ _) isOpen_univ (subset_univ _)
      R hR.contDiffOn
  obtain ⟨B,hB,hSupport,hRep⟩ := hCompactTheorem
  have hBound := affineScalar_rotation_generator_C1 i j ell
  have hFamilyTheorem := exists_rotated_remainder_weakEnergy_family R B hB hSupport hRep i j
    (14*‖ell‖) (by positivity) (fun z hz => (hBound z hz).1)
  obtain ⟨a,ha,S,hS,hz,hEquality,hFull,hWeak,hZero⟩ := hFamilyTheorem
  refine ⟨a,ha,S,hS,hz,?_,hFull.trans_eq (by ring),hWeak.trans_eq (by ring),hZero.trans_eq (by ring)⟩
  intro θ z hzB
  exact (hEquality θ z hzB).trans (coordinateRotationPrincipalFamily_scalar i j ell θ z)

/-- A fixed smooth compact matrix field equal to identity on the enlarged
    physical ball, suitable for actual common-support affine families. -/
theorem exists_compact_flat_matrix_field : ∃ A : X → Mat,ContDiff ℝ ∞ A ∧
    HasCompactSupport A ∧ ∀ z ∈ Metric.closedBall (0:X) 2,A z = 1 := by
  have hCutoff := (isCompact_closedBall (0:X) 2).exists_contDiff_cutoff isOpen_univ (subset_univ _)
  obtain ⟨ψ,hψ,hRange,hOne,hSupport,hSub⟩ := hCutoff
  let A : X → Mat := fun z => ψ z • (1:Mat)
  have hA : ContDiff ℝ ∞ A := hψ.smul contDiff_const
  have hAS : support A ⊆ tsupport ψ := by
    intro z hz
    apply subset_closure
    intro hψz
    exact hz (by simp only [A,hψz,zero_smul])
  refine ⟨A,hA,HasCompactSupport.of_support_subset_isCompact hSupport hAS,?_⟩
  intro z hz
  have hOneMem : z ∈ ψ ⁻¹' ({1}:Set ℝ) := interior_subset (hOne hz)
  have hOneAt : ψ z = 1 := hOneMem
  change ψ z • (1:Mat) = 1
  rw [hOneAt,one_smul]

end ShrinkingSpheres
