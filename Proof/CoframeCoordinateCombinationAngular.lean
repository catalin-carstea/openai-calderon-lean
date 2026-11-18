import Proof.CoordinateCombinationAngularFields
import Proof.CoframeScalarRotationCalculus
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.DirichletFamily OAI.AnisotropicCalderon.SphereHarmonic
lemma CoarseAngularFields.mulCoframe_angular (P : CoarseAngularFields) (g : MetricField)
    (a : X) (p : NormalFrameRelativeParameter) (i j : I) :
    (P.mulCoordinateCombination (fun k => normalFrameRelativeCoframeValue g a k p)).angular (i,j) =
      (P.angular (i,j)).comp (relativeCoframeNormalSobolevL 1 g a p)+
        P.operator.comp (relativeCoframeAngularSobolevL 1 g a i j p) := by
  apply ContinuousLinearMap.ext
  intro u
  simp only [CoarseAngularFields.mulCoordinateCombination,CoarseAngularFields.sum,
    CoarseAngularFields.smul,CoarseAngularFields.mulRight,coordinateScalarRotationData,
    relativeCoframeNormalSobolevL,relativeCoframeAngularSobolevL,
    coordinateAngularOneMul,_root_.sum_apply,_root_.smul_apply,_root_.add_apply,
    ContinuousLinearMap.comp_apply,map_sum,map_smul,smul_add,Finset.sum_add_distrib]
  rfl
end ShrinkingSpheres
