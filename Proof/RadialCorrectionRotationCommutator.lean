import Proof.RadialCorrectionRotationBlocks
import Proof.BoundaryAngularAdjoint
import Proof.ConormalFirstAdjoint

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
open OAI.AnisotropicCalderon.SphereHarmonic
open OAI.AnisotropicCalderon.SmoothSphereRotationProjection

theorem orderOneRotation_single (i j : I) (k : ℕ) (a : harmonicSphereSubspace k) :
    sphereSobolevRotationL 1 i j (sphereSobolevSingleL 1 k a) =
      sphereSobolevSingleL 0 k (harmonicSphereRotation k i j a) := by
  apply sphereSobolev_ext 0
  intro l
  rw [orderOneRotation_coefficient]
  by_cases hl : l=k
  · subst l
    rw [sphereSobolevCoefficientL_single_self,sphereSobolevCoefficientL_single_self]
  · rw [sphereSobolevCoefficientL_single_ne 1 k l hl,map_zero,
      sphereSobolevCoefficientL_single_ne 0 k l hl]

/-- Rotation covariance on the complete H1 domain, with the same correction
    acting on H1 and L2 through the proved inclusion compatibility. -/
theorem rotation_radialCorrection_commutator (i j : I) (q : X →L[ℝ] ℝ) :
    (sphereSobolevRotationL 1 i j).comp (radialCorrectionSobolevL 1 q)-
      (radialCorrectionCovectorL q).comp (sphereSobolevRotationL 1 i j) =
        (radialCorrectionCovectorL (rotationCovector q i j)).comp (sphereSobolevInclusionL 1 0 (by norm_num)) := by
  apply sphereSobolev_clm_eq_of_single 1
  intro k a
  change sphereSobolevRotationL 1 i j (radialCorrectionSobolevL 1 q (sphereSobolevSingleL 1 k a))-
      radialCorrectionCovectorL q (sphereSobolevRotationL 1 i j (sphereSobolevSingleL 1 k a)) =
        radialCorrectionCovectorL (rotationCovector q i j) (sphereSobolevInclusionL 1 0 (by norm_num) (sphereSobolevSingleL 1 k a))
  rw [orderOneRotation_single,sphereSobolevInclusionL_single,
    ← radialCorrectionSobolevL_zero q,← radialCorrectionSobolevL_zero (rotationCovector q i j)]
  cases k with
  | zero => simp only [radialCorrectionSobolevL_constant,map_zero,sub_zero]
  | succ m =>
    simp only [radialCorrectionSobolevL_single,orderOneRotation_single]
    exact ((sphereSobolevSingleL 0 m).map_sub _ _).symm.trans
      (congrArg (sphereSobolevSingleL 0 m) (harmonicRotation_radialDriftBlock_commutator m i j q a))

/-- Rotation covariance also holds for the physical L2 adjoint, proved by
    true adjunction and the skewness of rotations rather than formal transposition. -/
theorem rotation_radialCorrectionAdjoint_commutator (i j : I) (q : X →L[ℝ] ℝ) :
    (sphereSobolevRotationL 1 i j).comp (radialCorrectionAdjointSobolevL 1 q)-
      (radialCorrectionCovectorL q).adjoint.comp (sphereSobolevRotationL 1 i j) =
        (radialCorrectionCovectorL (rotationCovector q i j)).adjoint.comp (sphereSobolevInclusionL 1 0 (by norm_num)) := by
  apply boundary_operator_eq_of_inner
  intro u v
  let I0 := sphereSobolevInclusionL 1 0 (by norm_num)
  let R := sphereSobolevRotationL 1 i j
  let B := radialCorrectionCovectorL q
  let B1 := radialCorrectionSobolevL 1 q
  let C1 := radialCorrectionAdjointSobolevL 1 q
  let J := radialCorrectionCovectorL (rotationCovector q i j)
  have hFirst : ⟪R (C1 u),I0 v⟫_ℝ = -⟪I0 u,B (R v)⟫_ℝ := by
    rw [orderOneRotation_skew,radialCorrectionAdjointSobolevL_coarse,
      ContinuousLinearMap.adjoint_inner_left]
  have hSecond : ⟪B.adjoint (R u),I0 v⟫_ℝ = -⟪I0 u,R (B1 v)⟫_ℝ := by
    rw [ContinuousLinearMap.adjoint_inner_left,← radialCorrectionSobolevL_coarse q v,
      orderOneRotation_skew]
  have hForward : R (B1 v)-B (R v) = J (I0 v) := by
    exact congrArg (fun T : SphereSobolev 1 →L[ℝ] SphereSobolev 0 => T v)
      (rotation_radialCorrection_commutator i j q)
  change ⟪R (C1 u)-B.adjoint (R u),I0 v⟫_ℝ = ⟪J.adjoint (I0 u),I0 v⟫_ℝ
  have hBreak : ⟪R (C1 u)-B.adjoint (R u),I0 v⟫_ℝ =
      ⟪R (C1 u),I0 v⟫_ℝ-⟪B.adjoint (R u),I0 v⟫_ℝ := inner_sub_left _ _ _
  refine hBreak.trans ((congrArg₂ (fun x y : ℝ => x-y) hFirst hSecond).trans ?_)
  calc
    -⟪I0 u,B (R v)⟫_ℝ-(-⟪I0 u,R (B1 v)⟫_ℝ) = ⟪I0 u,R (B1 v)-B (R v)⟫_ℝ := by
      rw [inner_sub_right]
      ring
    _ = ⟪I0 u,J (I0 v)⟫_ℝ := congrArg (fun z : SphereSobolev 0 => ⟪I0 u,z⟫_ℝ) hForward
    _ = _ := (ContinuousLinearMap.adjoint_inner_left J (I0 v) (I0 u)).symm

end ShrinkingSpheres
