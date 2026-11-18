import Proof.ParallelScalarModelIdentity
import Proof.ParallelScalarModelDegreeSections
import Proof.ParallelScalarModelAngularAdjunction

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2800000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter
open scoped ContDiff Topology InnerProductSpace
namespace ShrinkingSpheres.ParallelEnergy
open OAI.AnisotropicCalderon.SphereHarmonic OAI.AnisotropicCalderon.DirichletFamily

def scalarModelForwardWeakSection (d : Data) (U : X → SphereSobolev (5/2:ℝ)) (y : X) :
    SphereSobolev (-(1/2:ℝ)) :=
  let U3 := sphereSobolevInclusionL (5/2:ℝ) (3/2:ℝ) (by norm_num) (U y);
  ∑ i : I,flatHalfRaisingL i (
    sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num) (fiveHalfCovariantDerivative d U (d.frame y i) y)+
    modelLogRadiusCoefficient d i y • degreeHigherL U3)

def scalarModelAdjointWeakSection (d : Data) (U : X → SphereSobolev (5/2:ℝ)) (y : X) :
    SphereSobolev (-(1/2:ℝ)) :=
  let U3 := sphereSobolevInclusionL (5/2:ℝ) (3/2:ℝ) (by norm_num) (U y);
  ∑ i : I,(flatHalfRaisingL i).adjoint (
    -sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num) (fiveHalfCovariantDerivative d U (d.frame y i) y)+
    modelLogRadiusCoefficient d i y • (degreeHigherL U3-
      sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num) U3))

lemma scalar_model_degree_coarse_half (U : X → SphereSobolev (5/2:ℝ)) (y : X) :
    sphereSobolevInclusionL 1 (1/2:ℝ) (by norm_num)
      (sphereSobolevShiftedDegreeL 2 (fiveHalfToTwoSection U y))=
      degreeHigherL (sphereSobolevInclusionL (5/2:ℝ) (3/2:ℝ) (by norm_num) (U y)) := by
  have h := sphereSobolevShiftedDegreeL_inclusion 2 (3/2:ℝ) (by norm_num) (fiveHalfToTwoSection U y)
  have hI : sphereSobolevInclusionL ((2:ℝ)-1) ((3/2:ℝ)-1) (by norm_num)=
      sphereSobolevInclusionL 1 (1/2:ℝ) (by norm_num) := by congr 1 <;> norm_num
  simpa only [hI,degreeHigherL,fiveHalfToTwoSection,sphereSobolevInclusionL_trans_apply] using h

lemma scalar_model_first_coarse_half (d : Data) (U : X → SphereSobolev (5/2:ℝ))
    (y v : X) (hU : DifferentiableAt ℝ U y) :
    sphereSobolevInclusionL 1 (1/2:ℝ) (by norm_num)
      (highSectionCovariantDerivative d (fiveHalfToTwoSection U) y v)=
    sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num) (fiveHalfCovariantDerivative d U v y) := by
  have h := congrArg (sphereSobolevInclusionL 1 (1/2:ℝ) (by norm_num))
    (fiveHalfCovariantDerivative_inclusion d U y v hU)
  simpa only [sphereSobolevInclusionL_trans_apply] using h.symm

lemma scalar_model_raising_weak_graph (d : Data) (U : X → SphereSobolev (5/2:ℝ))
    (y : X) (hU : DifferentiableAt ℝ U y) :
    sphereSobolevInclusionL 0 (-(1/2:ℝ)) (by norm_num)
      (modelRaisingSection d (fiveHalfToTwoSection U) y)=scalarModelForwardWeakSection d U y := by
  simp only [modelRaisingSection,scalarModelForwardWeakSection,map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [flatOneRaisingL_half,highSectionModelPlus,map_add,map_smul,
    scalar_model_first_coarse_half d U y (d.frame y i) hU,scalar_model_degree_coarse_half]
  rfl

lemma scalar_model_corrected_lowering_coarse_sum (d : Data) (V : X → SphereSobolev 2) (y : X) :
    modelLoweringSection d V y-modelAdjointDefectSection d V y=
      ∑ i : I,flatLoweringSobolevL 1 i (-highSectionCovariantDerivative d V y (d.frame y i)+
        modelLogRadiusCoefficient d i y • (sphereSobolevShiftedDegreeL 2 (V y)-
          sphereSobolevInclusionL 2 1 (by norm_num) (V y))) := by
  simp only [modelLoweringSection,modelAdjointDefectSection,← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  simp only [highSectionModelMinus,modelLogRadiusCoefficient,map_add,map_sub,map_neg,map_smul,smul_sub]
  abel

lemma scalar_model_corrected_lowering_weak_graph
    (Q : SmoothCoefficientJets 2)
    (hQ : ∀ z ∈ Metric.closedBall (0:X) 1,coefficientValue 2 Q =ᶠ[𝓝 z] (fun _ => (1:ℝ)))
    (d : Data) (U : X → SphereSobolev (5/2:ℝ)) (y : X) (hU : DifferentiableAt ℝ U y) :
    sphereSobolevInclusionL 0 (-(1/2:ℝ)) (by norm_num)
      (modelLoweringSection d (fiveHalfToTwoSection U) y-
        modelAdjointDefectSection d (fiveHalfToTwoSection U) y)=scalarModelAdjointWeakSection d U y := by
  rw [scalar_model_corrected_lowering_coarse_sum,map_sum]
  change (∑ i : I,_)=∑ i : I,_
  apply Finset.sum_congr rfl
  intro i _
  let z : SphereSobolev 1 := -highSectionCovariantDerivative d (fiveHalfToTwoSection U) y (d.frame y i)+
    modelLogRadiusCoefficient d i y • (sphereSobolevShiftedDegreeL 2 (fiveHalfToTwoSection U y)-
      sphereSobolevInclusionL 2 1 (by norm_num) (fiveHalfToTwoSection U y))
  have hAdj := DFunLike.congr_fun (flat_lowering_coarse_half_graph Q hQ i) z
  simp only [ContinuousLinearMap.comp_apply] at hAdj
  apply hAdj.trans
  congr 1
  simp only [z,map_add,map_neg,map_smul,map_sub,
    scalar_model_first_coarse_half d U y (d.frame y i) hU,scalar_model_degree_coarse_half U y]
  simp only [fiveHalfToTwoSection,sphereSobolevInclusionL_trans_apply]

end ShrinkingSpheres.ParallelEnergy
