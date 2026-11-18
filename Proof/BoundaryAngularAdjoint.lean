import Proof.CoarseCoefficientCompatibility
import Proof.Archive.NativeBoundaryCoefficientL2Decomposition

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxSynthPendingDepth 15
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set
open scoped ENNReal InnerProductSpace
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.EnergyBridge OAI.AnisotropicCalderon.DirichletFamily
open OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open OAI.AnisotropicCalderon.SphereHarmonic
open OAI.AnisotropicCalderon.SpectralWeightedGraph
open OAI.AnisotropicCalderon.SmoothSphereRotationProjection
open OAI.AnisotropicCalderon.NativeCoefficientBoundaryMultiplier

def oneSphereCoordinateMulL (i : I) : SphereSobolev 1 →L[ℝ] SphereSobolev 1 :=
  sphereSobolevLinearCoordinateMulL sphereFischerInner orthogonalSphereHarmonics denseSphereHarmonics
    1 (EuclideanSpace.single i 1)

theorem oneSphereCoordinateMulL_coarse (i : I) (u : SphereSobolev 1) :
    sphereSobolevInclusionL 1 0 (by norm_num) (oneSphereCoordinateMulL i u) =
      coarseSphereScalarMulL (sphereCoordinate i) (sphereSobolevInclusionL 1 0 (by norm_num) u) := by
  let Z := sphereSobolevZeroEquiv orthogonalSphereHarmonics denseSphereHarmonics
  let v := Z.symm (sphereSobolevInclusionL 1 0 (by norm_num) u)
  have h := sphereSobolevInclusionL_linearCoordinateMul_zeroEquiv sphereFischerInner orthogonalSphereHarmonics
    denseSphereHarmonics 1 (by norm_num) (EuclideanSpace.single i 1) u v (Z.apply_symm_apply _).symm
  have hA := (sphereLinearCoordinateMulL_single i).trans (sphereCoordinateMulL_eq_scalarMulL i)
  exact h.trans (congrArg (fun A : SphereL2 →L[ℝ] SphereL2 => Z (A v)) hA)

theorem orderOneRotation_skew (u v : SphereSobolev 1) (i j : I) :
    ⟪sphereSobolevRotationL 1 i j u,sphereSobolevInclusionL 1 0 (by norm_num) v⟫_ℝ =
      -⟪sphereSobolevInclusionL 1 0 (by norm_num) u,sphereSobolevRotationL 1 i j v⟫_ℝ := by
  rw [inner_sphereSobolev 0,inner_sphereSobolev 0,← tsum_neg]
  apply tsum_congr
  intro k
  simp only [besselWeight_zero_order,one_pow,one_mul,sphereSobolevCoefficientL_inclusion,orderOneRotation_coefficient]
  exact inner_harmonicSphereRotation_skew k i j _ _

def coarseBoundaryTangentialL (F : I → SmoothCoefficientJets 2) : SphereSobolev 1 →L[ℝ] SphereSobolev 0 :=
  ∑ j : I,∑ i : I,(coarseSphereScalarMulL (smoothSphereValue (coefficientSmoothData (F j)))).comp
    ((coarseSphereScalarMulL (sphereCoordinate i)).comp (sphereSobolevRotationL 1 i j))

def adjointBoundaryTangentialL (F : I → SmoothCoefficientJets 2) : SphereSobolev 1 →L[ℝ] SphereSobolev 0 :=
  ∑ j : I,∑ i : I,-(sphereSobolevRotationL 1 i j).comp
    ((oneSphereCoordinateMulL i).comp (oneBoundaryCoefficientMulL (F j)))

def boundaryTangentialAdjointBudget : ℝ :=
  ∑ j : I,∑ i : I,‖sphereSobolevRotationL 1 i j‖*‖oneSphereCoordinateMulL i‖

lemma boundaryTangentialAdjointBudget_nonneg : 0 ≤ boundaryTangentialAdjointBudget := by
  unfold boundaryTangentialAdjointBudget
  positivity

/-- Exact physical L2 adjunction for a tangential coefficient action. Writing
    it through rotations keeps every differentiated coefficient in its H1 map. -/
theorem boundaryTangentialL_adjoint (F : I → SmoothCoefficientJets 2) (u v : SphereSobolev 1) :
    ⟪coarseBoundaryTangentialL F u,sphereSobolevInclusionL 1 0 (by norm_num) v⟫_ℝ =
      ⟪sphereSobolevInclusionL 1 0 (by norm_num) u,adjointBoundaryTangentialL F v⟫_ℝ := by
  let I0 := sphereSobolevInclusionL 1 0 (by norm_num)
  have hTerm (j i : I) :
      ⟪coarseSphereScalarMulL (smoothSphereValue (coefficientSmoothData (F j)))
        (coarseSphereScalarMulL (sphereCoordinate i) (sphereSobolevRotationL 1 i j u)),I0 v⟫_ℝ =
      ⟪I0 u,-sphereSobolevRotationL 1 i j (oneSphereCoordinateMulL i (oneBoundaryCoefficientMulL (F j) v))⟫_ℝ := by
    have hMul : I0 (oneSphereCoordinateMulL i (oneBoundaryCoefficientMulL (F j) v)) =
        coarseSphereScalarMulL (sphereCoordinate i)
          (coarseSphereScalarMulL (smoothSphereValue (coefficientSmoothData (F j))) (I0 v)) :=
      (oneSphereCoordinateMulL_coarse i _).trans
        (congrArg (coarseSphereScalarMulL (sphereCoordinate i)) (oneBoundaryCoefficientMulL_coarse (F j) v))
    exact (coarseSphereScalarMulL_symmetric _ _ _).trans
      ((coarseSphereScalarMulL_symmetric _ _ _).trans
        ((congrArg (fun z : SphereSobolev 0 => ⟪sphereSobolevRotationL 1 i j u,z⟫_ℝ) hMul).symm.trans
          ((orderOneRotation_skew u _ i j).trans (inner_neg_right _ _).symm)))
  simp only [coarseBoundaryTangentialL,adjointBoundaryTangentialL,_root_.sum_apply,
    ContinuousLinearMap.comp_apply,_root_.neg_apply,sum_inner,inner_sum]
  exact Finset.sum_congr rfl (fun j _ => Finset.sum_congr rfl (fun i _ => hTerm j i))

theorem norm_adjointBoundaryTangentialL_le (F : I → SmoothCoefficientJets 2) (q : ℝ) (hq : 0 ≤ q)
    (hF : ∀ j,‖oneBoundaryCoefficientMulL (F j)‖ ≤ q) :
    ‖adjointBoundaryTangentialL F‖ ≤ boundaryTangentialAdjointBudget*q := by
  have hTerm (j i : I) : ‖-(sphereSobolevRotationL 1 i j).comp
      ((oneSphereCoordinateMulL i).comp (oneBoundaryCoefficientMulL (F j)))‖ ≤
      (‖sphereSobolevRotationL 1 i j‖*‖oneSphereCoordinateMulL i‖)*q := by
    rw [norm_neg]
    exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
      ((mul_le_mul_of_nonneg_left ((ContinuousLinearMap.opNorm_comp_le _ _).trans
        (mul_le_mul_of_nonneg_left (hF j) (norm_nonneg _))) (norm_nonneg _)).trans_eq (by ring))
  calc
    _ ≤ ∑ j : I,∑ i : I,‖-(sphereSobolevRotationL 1 i j).comp
        ((oneSphereCoordinateMulL i).comp (oneBoundaryCoefficientMulL (F j)))‖ :=
      (norm_sum_le _ _).trans (Finset.sum_le_sum (fun j _ => norm_sum_le _ _))
    _ ≤ ∑ j : I,∑ i : I,(‖sphereSobolevRotationL 1 i j‖*‖oneSphereCoordinateMulL i‖)*q :=
      Finset.sum_le_sum (fun j _ => Finset.sum_le_sum (fun i _ => hTerm j i))
    _ = _ := by unfold boundaryTangentialAdjointBudget;rw [Finset.sum_mul];simp_rw [Finset.sum_mul]

end ShrinkingSpheres
