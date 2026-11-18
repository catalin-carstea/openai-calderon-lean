import Proof.ParallelScalarModelDegreeSections
import Proof.ParallelScalarModelCoordinateWeak
import Proof.ParallelScalarModelRaising
import Proof.ParallelModelFirstRaisingComm

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2800000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
open Set Filter
open scoped ContDiff Topology InnerProductSpace
namespace ShrinkingSpheres.ParallelEnergy
open OAI.AnisotropicCalderon.SphereHarmonic OAI.AnisotropicCalderon.DirichletFamily

def modelFirstModelForwardHalf (d : Data) (U : X → SphereSobolev (5/2:ℝ)) (y : X) : SphereSobolev (1/2:ℝ) :=
  ∑ k : I,∑ c : I,(d.γ y)⁻¹ k c • (
    framedRaisingHigherL d y (axis c) (fiveHalfCovariantDerivative d U (axis k) y)+
    coordDeriv k (fun x => Real.log (d.radius x)) y •
      framedRaisingHigherL d y (axis c) (scalarModelDegreeSection U y))

def modelFirstModelAdjointHalf
    (A : I → SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ))
    (d : Data) (U : X → SphereSobolev (5/2:ℝ)) (y : X) : SphereSobolev (1/2:ℝ) :=
  ∑ k : I,∑ c : I,(d.γ y)⁻¹ k c • (
    -scalarModelRaisingAdjointHigher A d c y (fiveHalfCovariantDerivative d U (axis k) y)+
    coordDeriv k (fun x => Real.log (d.radius x)) y •
      scalarModelRaisingAdjointHigher A d c y (scalarModelShiftedDegreeSection U y))

lemma modelFirstModelForwardHalf_weak (d : Data) (U : X → SphereSobolev (5/2:ℝ)) (y : X)
    (hFrame : ∀ i j,metricPair d.γ y (d.frame y i) (d.frame y j)=if i=j then 1 else 0) :
    sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num) (modelFirstModelForwardHalf d U y)=
      scalarModelForwardWeakSection d U y := by
  have hR (c : I) (v : SphereSobolev (3/2:ℝ)) := DFunLike.congr_fun (framedRaisingHalf_balanced d y (axis c)) v
  simp only [ContinuousLinearMap.comp_apply] at hR
  rw [scalarModelForwardWeakSection_coordinate d U y hFrame]
  simp only [modelFirstModelForwardHalf,map_sum,map_smul,map_add,hR,scalarModelDegreeSection_half_inclusion]

lemma modelFirstModelAdjointHalf_weak
    (A : I → SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ))
    (d : Data) (U : X → SphereSobolev (5/2:ℝ)) (y : X)
    (hFrame : ∀ i j,metricPair d.γ y (d.frame y i) (d.frame y j)=if i=j then 1 else 0)
    (hA : ∀ i,(sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)).comp (A i)=
      (flatHalfRaisingL i).adjoint.comp (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num))) :
    sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num) (modelFirstModelAdjointHalf A d U y)=
      scalarModelAdjointWeakSection d U y := by
  have hR (c : I) (v : SphereSobolev (3/2:ℝ)) :=
    DFunLike.congr_fun (scalarModelRaisingAdjointHigher_balanced A d c y hA) v
  simp only [ContinuousLinearMap.comp_apply] at hR
  have hD : sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num) (scalarModelShiftedDegreeSection U y)=
      degreeHigherL (sphereSobolevInclusionL (5/2:ℝ) (3/2:ℝ) (by norm_num) (U y))-
        sphereSobolevInclusionL (5/2:ℝ) (1/2:ℝ) (by norm_num) (U y) := by
    rw [scalarModelShiftedDegreeSection,map_sub,scalarModelDegreeSection_half_inclusion,sphereSobolevInclusionL_trans_apply]
  rw [scalarModelAdjointWeakSection_coordinate d U y hFrame]
  simp only [modelFirstModelAdjointHalf,map_sum,map_smul,map_add,map_neg,hR,hD]

lemma modelFirstModelForwardHalf_coarse (d : Data) (U : X → SphereSobolev (5/2:ℝ)) (y : X)
    (hU : DifferentiableAt ℝ U y)
    (hFrame : ∀ i j,metricPair d.γ y (d.frame y i) (d.frame y j)=if i=j then 1 else 0) :
    sphereSobolevInclusionL (1/2:ℝ) 0 (by norm_num) (modelFirstModelForwardHalf d U y)=
      modelRaisingSection d (fiveHalfToTwoSection U) y := by
  apply sphereSobolevInclusionL_injective 0 (-(1/2:ℝ)) (by norm_num)
  rw [sphereSobolevInclusionL_trans_apply,modelFirstModelForwardHalf_weak d U y hFrame,
    scalar_model_raising_weak_graph d U y hU]

lemma modelFirstModelAdjointHalf_coarse
    (Q : SmoothCoefficientJets 2)
    (hQ : ∀ z ∈ Metric.closedBall (0:X) 1,coefficientValue 2 Q =ᶠ[𝓝 z] (fun _ => (1:ℝ)))
    (A : I → SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ))
    (d : Data) (U : X → SphereSobolev (5/2:ℝ)) (y : X) (hU : DifferentiableAt ℝ U y)
    (hFrame : ∀ i j,metricPair d.γ y (d.frame y i) (d.frame y j)=if i=j then 1 else 0)
    (hA : ∀ i,(sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)).comp (A i)=
      (flatHalfRaisingL i).adjoint.comp (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num))) :
    sphereSobolevInclusionL (1/2:ℝ) 0 (by norm_num) (modelFirstModelAdjointHalf A d U y)=
      modelLoweringSection d (fiveHalfToTwoSection U) y-modelAdjointDefectSection d (fiveHalfToTwoSection U) y := by
  apply sphereSobolevInclusionL_injective 0 (-(1/2:ℝ)) (by norm_num)
  rw [sphereSobolevInclusionL_trans_apply,modelFirstModelAdjointHalf_weak A d U y hFrame hA,
    scalar_model_corrected_lowering_weak_graph Q hQ d U y hU]

end ShrinkingSpheres.ParallelEnergy
