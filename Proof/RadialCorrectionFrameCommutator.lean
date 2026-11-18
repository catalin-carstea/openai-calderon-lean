import Proof.RadialCorrectionRotationCommutator
import Proof.CanonicalFirstRadialFamily

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxSynthPendingDepth 15
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter MeasureTheory
open scoped ENNReal Topology InnerProductSpace
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.EnergyBridge OAI.AnisotropicCalderon.DirichletFamily
open OAI.AnisotropicCalderon.SphereHarmonic OAI.AnisotropicCalderon.SmoothSphereRotation

/-- The angular part of the actual horizontal derivative in frame coordinates. -/
def angularConnectionL (A : I → I → ℝ) : SphereSobolev 1 →L[ℝ] SphereSobolev 0 :=
  ∑ i : I,∑ j : I,(-(1/2:ℝ)*A i j) • sphereSobolevRotationL 1 i j

theorem frameAngular_covector_decomposition (A : I → I → ℝ) (hA : ∀ i j,A i j = -A j i)
    (q : X →L[ℝ] ℝ) :
    q.comp (frameAngularLinear A) = ∑ i : I,∑ j : I,(-(1/2:ℝ)*A i j) • rotationCovector q i j := by
  apply ContinuousLinearMap.ext
  intro z
  rw [ContinuousLinearMap.comp_apply,frameAngularLinear_apply,frameAngularVector_eq_rotation A hA z,map_sum]
  simp only [map_sum,map_smul,_root_.sum_apply,_root_.smul_apply]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  apply congrArg (fun t : ℝ => (-(1/2:ℝ)*A i j) • t)
  simp only [rotationVector,rotationCovector,map_sub,map_smul,_root_.sub_apply,_root_.smul_apply,
    PiLp.proj_apply,smul_eq_mul,axis]
  ring

theorem radialCorrectionCovectorL_frame_action_sum (A : I → I → ℝ) (hA : ∀ i j,A i j = -A j i)
    (q : X →L[ℝ] ℝ) :
    (∑ i : I,∑ j : I,(-(1/2:ℝ)*A i j) • radialCorrectionCovectorL (rotationCovector q i j)) =
      radialCorrectionCovectorL (q.comp (frameAngularLinear A)) := by
  rw [frameAngular_covector_decomposition A hA q]
  simp only [map_sum,map_smul]

theorem angularConnection_commutator_of_rotations (A : I → I → ℝ)
    (B1 : SphereSobolev 1 →L[ℝ] SphereSobolev 1) (B0 : SphereSobolev 0 →L[ℝ] SphereSobolev 0)
    (J : I → I → SphereSobolev 0 →L[ℝ] SphereSobolev 0)
    (hComm : ∀ i j,(sphereSobolevRotationL 1 i j).comp B1-B0.comp (sphereSobolevRotationL 1 i j) =
      (J i j).comp (sphereSobolevInclusionL 1 0 (by norm_num))) :
    (angularConnectionL A).comp B1-B0.comp (angularConnectionL A) =
      (∑ i : I,∑ j : I,(-(1/2:ℝ)*A i j) • J i j).comp (sphereSobolevInclusionL 1 0 (by norm_num)) := by
  apply ContinuousLinearMap.ext
  intro u
  change angularConnectionL A (B1 u)-B0 (angularConnectionL A u) =
    (∑ i : I,∑ j : I,(-(1/2:ℝ)*A i j) • J i j) (sphereSobolevInclusionL 1 0 (by norm_num) u)
  simp only [angularConnectionL,_root_.sum_apply,_root_.smul_apply,map_sum,map_smul]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro j _
  rw [← smul_sub]
  exact congrArg (fun z : SphereSobolev 0 => (-(1/2:ℝ)*A i j) • z)
    (congrArg (fun T : SphereSobolev 1 →L[ℝ] SphereSobolev 0 => T u) (hComm i j))

/-- Exact rotation covariance for the actual frame connection, with no bound
    on its size and therefore no frame-derivative hypothesis. -/
theorem angularConnection_radialCorrection_commutator (A : I → I → ℝ) (hA : ∀ i j,A i j = -A j i)
    (q : X →L[ℝ] ℝ) :
    (angularConnectionL A).comp (radialCorrectionSobolevL 1 q)-
      (radialCorrectionCovectorL q).comp (angularConnectionL A) =
        (radialCorrectionCovectorL (q.comp (frameAngularLinear A))).comp (sphereSobolevInclusionL 1 0 (by norm_num)) := by
  have hJ : (∑ i : I,∑ j : I,(-(1/2:ℝ)*A i j) • radialCorrectionCovectorL (rotationCovector q i j)) =
      radialCorrectionCovectorL (q.comp (frameAngularLinear A)) := by
    rw [frameAngular_covector_decomposition A hA q]
    simp only [map_sum,map_smul]
  exact (angularConnection_commutator_of_rotations A _ _ _ (fun i j => rotation_radialCorrection_commutator i j q)).trans
    (congrArg (fun T : SphereSobolev 0 →L[ℝ] SphereSobolev 0 => T.comp (sphereSobolevInclusionL 1 0 (by norm_num))) hJ)

theorem angularConnection_radialCorrectionAdjoint_commutator (A : I → I → ℝ) (hA : ∀ i j,A i j = -A j i)
    (q : X →L[ℝ] ℝ) :
    (angularConnectionL A).comp (radialCorrectionAdjointSobolevL 1 q)-
      (radialCorrectionCovectorL q).adjoint.comp (angularConnectionL A) =
        (radialCorrectionCovectorL (q.comp (frameAngularLinear A))).adjoint.comp (sphereSobolevInclusionL 1 0 (by norm_num)) := by
  have hJ : (∑ i : I,∑ j : I,(-(1/2:ℝ)*A i j) • (radialCorrectionCovectorL (rotationCovector q i j)).adjoint) =
      (radialCorrectionCovectorL (q.comp (frameAngularLinear A))).adjoint := by
    let Adj : (SphereSobolev 0 →L[ℝ] SphereSobolev 0) →L[ℝ] (SphereSobolev 0 →L[ℝ] SphereSobolev 0) :=
      (ContinuousLinearMap.adjoint : (SphereSobolev 0 →L[ℝ] SphereSobolev 0) ≃ₗᵢ[ℝ]
        (SphereSobolev 0 →L[ℝ] SphereSobolev 0)).toContinuousLinearEquiv.toContinuousLinearMap
    have h := congrArg Adj (radialCorrectionCovectorL_frame_action_sum A hA q)
    simp only [map_sum,map_smul] at h
    exact h
  exact (angularConnection_commutator_of_rotations A _ _ _ (fun i j => rotation_radialCorrectionAdjoint_commutator i j q)).trans
    (congrArg (fun T : SphereSobolev 0 →L[ℝ] SphereSobolev 0 => T.comp (sphereSobolevInclusionL 1 0 (by norm_num))) hJ)

end ShrinkingSpheres
