import Proof.ClosedScalarCoordinateCommutation
import Proof.RelativeCoframeSobolevMultiplier
import Proof.CoordinateScalarRotationPacket
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2600000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
open Set
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.DirichletFamily
open OAI.AnisotropicCalderon.SphereHarmonic

lemma clm_commute_sum_smul {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (A : E →L[ℝ] E) (q : I → ℝ) (B : I → E →L[ℝ] E)
    (h : ∀ j,A.comp (B j) = (B j).comp A) :
    A.comp (∑ j : I,q j • B j) = (∑ j : I,q j • B j).comp A := by
  apply ContinuousLinearMap.ext
  intro u
  simp only [ContinuousLinearMap.comp_apply,_root_.sum_apply,_root_.smul_apply,map_sum,map_smul]
  apply Finset.sum_congr rfl
  intro j hj
  exact congrArg (fun z : E => q j • z) (congrArg (fun T : E →L[ℝ] E => T u) (h j))

lemma closedOneScalar_coframe_commute (Q : ClosedCoefficientJets 3)
    (g : MetricField) (v : X) (p : NormalFrameRelativeParameter) :
    (closedOneBoundaryScalarMultiplierL Q).comp (relativeCoframeNormalSobolevL 1 g v p) =
      (relativeCoframeNormalSobolevL 1 g v p).comp (closedOneBoundaryScalarMultiplierL Q) :=
  clm_commute_sum_smul _ _ _ (closedOneBoundaryScalarMultiplier_coordinate_commute Q)

lemma oneCoordinate_coframe_commute (j : I) (g : MetricField) (v : X) (p : NormalFrameRelativeParameter) :
    (coordinateMultiplierSobolevL 1 j).comp (relativeCoframeNormalSobolevL 1 g v p) =
      (relativeCoframeNormalSobolevL 1 g v p).comp (coordinateMultiplierSobolevL 1 j) :=
  clm_commute_sum_smul _ _ _ (coordinateMultiplier_one_commute j)

lemma relativeCoframeNormal_one_commute (g : MetricField) (a v : X) (p : NormalFrameRelativeParameter) :
    (relativeCoframeNormalSobolevL 1 g a p).comp (relativeCoframeNormalSobolevL 1 g v p) =
      (relativeCoframeNormalSobolevL 1 g v p).comp (relativeCoframeNormalSobolevL 1 g a p) :=
  clm_commute_sum_smul _ _ _ (fun j => (oneCoordinate_coframe_commute j g a p).symm)

def relativeCoframeAngularSobolevL (s : ℝ) (g : MetricField) (v : X) (i j : I)
    (p : NormalFrameRelativeParameter) : SphereSobolev s →L[ℝ] SphereSobolev s :=
  ∑ k : I,normalFrameRelativeCoframeValue g v k p •
    ((if k=j then coordinateMultiplierSobolevL s i else 0)-
      (if k=i then coordinateMultiplierSobolevL s j else 0))

lemma relativeCoframeAngularSobolev_inclusion (s t : ℝ) (hst : t ≤ s)
    (g : MetricField) (v : X) (i j : I) (p : NormalFrameRelativeParameter) (u : SphereSobolev s) :
    sphereSobolevInclusionL s t hst (relativeCoframeAngularSobolevL s g v i j p u) =
      relativeCoframeAngularSobolevL t g v i j p (sphereSobolevInclusionL s t hst u) := by
  simp only [relativeCoframeAngularSobolevL,_root_.sum_apply,_root_.smul_apply,map_sum,map_smul]
  apply Finset.sum_congr rfl
  intro k hk
  congr 1
  split_ifs <;> simp only [_root_.sub_apply,_root_.zero_apply,map_sub,map_zero,
    coordinateMultiplierSobolevL,sphereSobolevInclusionL_linearCoordinateMul]

lemma rotation_coframe_product (g : MetricField) (v : X) (i j : I)
    (p : NormalFrameRelativeParameter) (u : SphereSobolev 1) :
    sphereSobolevRotationL 1 i j (relativeCoframeNormalSobolevL 1 g v p u) =
      relativeCoframeAngularSobolevL 0 g v i j p (sphereSobolevInclusionL 1 0 (by norm_num) u)+
        relativeCoframeNormalSobolevL 0 g v p (sphereSobolevRotationL 1 i j u) := by
  have hEach (k : I) := (coordinateScalarRotationData k).product (i,j) u
  change ∀ k : I,sphereSobolevRotationL 1 i j (oneSphereCoordinateMulL k u) =
    coordinateAngularCoarseMul i j k (sphereSobolevInclusionL 1 0 (by norm_num) u)+
      coarseSphereScalarMulL (sphereCoordinate k) (sphereSobolevRotationL 1 i j u) at hEach
  simp only [relativeCoframeNormalSobolevL,relativeCoframeAngularSobolevL,
    _root_.sum_apply,_root_.smul_apply,map_sum,map_smul]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro k hk
  have hCoord : coordinateMultiplierSobolevL 1 k = oneSphereCoordinateMulL k := rfl
  rw [hCoord,hEach k,smul_add]
  simp only [coordinateMultiplierSobolevL_zero]
  congr 1
end ShrinkingSpheres
