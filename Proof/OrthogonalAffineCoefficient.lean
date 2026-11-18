import Proof.CompactRotatedRemainderOperator

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1400000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter
open scoped ContDiff Topology Matrix.Norms.Elementwise
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.EnergyBridge OAI.AnisotropicCalderon.DirichletFamily
open OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open OAI.AnisotropicCalderon.MetricOperator OAI.AnisotropicCalderon.MetricVolume
open OAI.AnisotropicCalderon.SmoothSphereRotation

lemma orthogonalPrincipalCoefficient_scalar (e : X ≃ₗᵢ[ℝ] X) (s : X → ℝ) (z : X) :
    orthogonalPrincipalCoefficient e (fun w => s w • (1:Mat)) z = s (e z) • (1:Mat) := by
  have hScalar (c : ℝ) : matrixOperatorMap (c • (1:Mat)) = c • ContinuousLinearMap.id ℝ X := by
    change matrixOperatorAlgEquiv (c • (1:Mat)) = c • (1 : X →L[ℝ] X)
    rw [map_smul,map_one]
  unfold orthogonalPrincipalCoefficient
  rw [hScalar]
  have hCancel : e.symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
      ((s (e z) • ContinuousLinearMap.id ℝ X).comp e.toContinuousLinearEquiv.toContinuousLinearMap) =
      s (e z) • ContinuousLinearMap.id ℝ X := by
    apply ContinuousLinearMap.ext
    intro v
    change e.symm (s (e z) • e v) = s (e z) • v
    rw [map_smul,e.symm_apply_apply]
  rw [hCancel]
  change matrixOperatorAlgEquiv.symm (s (e z) • (1 : X →L[ℝ] X)) = s (e z) • (1:Mat)
  rw [map_smul,map_one]

lemma coordinateRotationPrincipalFamily_scalar (i j : I) (s : X → ℝ) (θ : ℝ) (z : X) :
    coordinateRotationPrincipalFamily i j (fun v : ℝ × X => s v.2 • (1:Mat)) ((θ,0),z) =
      s (coordinateRotation i j θ z) • (1:Mat) := by
  rw [coordinateRotationPrincipalFamily_eq_orthogonal,orthogonalPrincipalCoefficient_scalar]
  rfl

/-- Orthogonal rotation retains the same scalar center and transports the
    affine first correction. The actual quadratic coefficient remainder is
    the shared residual in this exact whole-angle identity. -/
theorem rotated_affineMatrixRemainder_identity (i j : I) (a : X → Mat)
    (c r : ℝ) (ell : X →L[ℝ] ℝ) (θ : ℝ) (z : X) :
    coordinateRotationPrincipalFamily i j (fun v : ℝ × X => a v.2) ((θ,0),z) =
      c • (1:Mat)+r • (ell (coordinateRotation i j θ z) • (1:Mat))+
        coordinateRotationPrincipalFamily i j
          (fun v : ℝ × X => affineMatrixRemainder a c r ell v.2) ((θ,0),z) := by
  have hScalar := coordinateRotationPrincipalFamily_scalar i j (fun w => c+r*ell w) θ z
  simp only [coordinateRotationPrincipalFamily,affineMatrixRemainder] at hScalar ⊢
  rw [Matrix.mul_sub,Matrix.sub_mul]
  rw [hScalar]
  module

/-- A canonical affine scalar coefficient has a uniform local C1 rotation
    generator bound controlled by the norm of its linear form alone. -/
theorem affineScalar_rotation_generator_C1 (i j : I) (ell : X →L[ℝ] ℝ) :
    ∀ z ∈ (ballOpens:Set X),
      ‖rotationPrincipalCoefficientDerivative i j (fun w => ell w • (1:Mat)) z‖ ≤ 14*‖ell‖ ∧
      ‖fderiv ℝ (rotationPrincipalCoefficientDerivative i j (fun w => ell w • (1:Mat))) z‖ ≤ 14*‖ell‖ := by
  let C : ℝ →L[ℝ] Mat := ContinuousLinearMap.toSpanSingleton ℝ (1:Mat)
  let L : X →L[ℝ] Mat := C.comp ell
  have hC : ‖C‖ ≤ 1 := by
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro t
    change ‖t • (1:Mat)‖ ≤ 1*‖t‖
    rw [norm_smul]
    have hOne : ‖(1:Mat)‖ ≤ 1 := by
      apply (Matrix.norm_le_iff zero_le_one).mpr
      intro i j
      by_cases h : i=j <;> simp [Matrix.one_apply,h]
    exact (mul_le_mul_of_nonneg_left hOne (norm_nonneg t)).trans_eq (by ring)
  have hL : ‖L‖ ≤ ‖ell‖ := (ContinuousLinearMap.opNorm_comp_le C ell).trans
    ((mul_le_mul_of_nonneg_right hC (norm_nonneg ell)).trans_eq (by ring))
  have hEq : (fun w => ell w • (1:Mat)) = L := rfl
  rw [hEq]
  intro z hz
  have hzN : ‖z‖ ≤ 1 := by
    change z ∈ Metric.ball (0:X) 1 at hz
    have hN : ‖z‖ < 1 := by simpa only [Metric.mem_ball,dist_zero_right] using hz
    exact hN.le
  have hFirst : ‖fderiv ℝ L z‖ ≤ ‖ell‖ := by rw [L.fderiv];exact hL
  have hSecond : ‖fderiv ℝ (fderiv ℝ L) z‖ ≤ 0 := by
    have hConst : fderiv ℝ L = fun _ => L := funext (fun w => L.fderiv)
    rw [hConst,fderiv_const_apply,norm_zero]
  have hSmooth : ContDiff ℝ ∞ L := L.contDiff
  constructor
  · apply (Matrix.norm_le_iff (by positivity : 0 ≤ 14*‖ell‖)).mpr
    intro k l
    have hVal (k l : I) : |L z k l| ≤ ‖ell‖ :=
      (Matrix.norm_entry_le_entrywise_sup_norm (L z) (i:=k) (j:=l)).trans
        ((L.le_opNorm z).trans ((mul_le_mul hL hzN (norm_nonneg _) (norm_nonneg _)).trans_eq (by ring)))
    have h := rotationPrincipalCoefficientDerivative_entry_bound i j L z ‖ell‖ ‖ell‖
      (norm_nonneg _) (norm_nonneg _) hVal hFirst k l
    exact h.trans (by nlinarith [mul_le_mul_of_nonneg_left hzN (norm_nonneg ell)])
  · exact (norm_fderiv_rotationPrincipalCoefficientDerivative_le i j L z L.differentiableAt
      ((hSmooth.fderiv_right (m:=1) (by simp)).differentiable (by norm_num) z)
      ‖ell‖ 0 (norm_nonneg _) le_rfl hFirst hSecond).trans_eq (by ring)

/-- The scalar affine first correction has a genuine compact whole-angle
    family, with exactly its rotated coefficient on the closed ball and
    native operator derivative constants linear in its covector norm. -/
theorem exists_rotated_linear_scalar_operator_family (i j : I) (ell : X →L[ℝ] ℝ) :
    ∃ a : ℝ × X → Mat,∃ ha : ContDiff ℝ ∞ a,∃ S : Set X,∃ hS : IsCompact S,
      ∃ hz : ∀ θ z,z ∉ S → a (θ,z) = 0,
      (∀ θ z,z ∈ Metric.closedBall (0:X) 2 →
        a (θ,z) = ell (coordinateRotation i j θ z) • (1:Mat)) ∧
      ‖fderiv ℝ (fun θ => strongDirichletOperator fixedSobolevCalculus 0
        (commonSupportMatrixFamily 2 a ha S hS hz θ)) 0‖ ≤
          28*strongC1OperatorBudget fixedSobolevCalculus*‖ell‖ ∧
      ‖fderiv ℝ (fun θ => fullCoefficientOperatorL fixedSobolevCalculus 0
        (commonSupportMatrixFamily 2 a ha S hS hz θ)) 0‖ ≤
          28*fullC1OperatorBudget fixedSobolevCalculus*‖ell‖ := by
  let R : X → Mat := fun z => ell z • (1:Mat)
  have hR : ContDiff ℝ ∞ R := ell.contDiff.smul contDiff_const
  obtain ⟨B,hB,hSupport,hRep⟩ := exists_contDiff_eq_near_compact_of_contDiffOn
    (Metric.closedBall (0:X) 2) Set.univ (isCompact_closedBall _ _) isOpen_univ (subset_univ _)
      R hR.contDiffOn
  have hBound := affineScalar_rotation_generator_C1 i j ell
  obtain ⟨a,ha,S,hS,hz,hEquality,hStrong,hFull⟩ := exists_rotated_remainder_operator_family
    R B hB hSupport hRep i j (14*‖ell‖) (by positivity)
      (fun z hz => (hBound z hz).1) (fun z hz => (hBound z hz).2)
  refine ⟨a,ha,S,hS,hz,?_,hStrong.trans_eq (by ring),hFull.trans_eq (by ring)⟩
  intro θ z hzB
  exact (hEquality θ z hzB).trans (coordinateRotationPrincipalFamily_scalar i j ell θ z)

end ShrinkingSpheres
