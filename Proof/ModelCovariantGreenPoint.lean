import Proof.ContractedLoweringCovariantPair
import Proof.OneSectionCovariantVectorGreen
import Proof.ModelCovariantSections

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2600000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set
open scoped ContDiff Topology InnerProductSpace
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.SphereHarmonic
open OAI.AnisotropicCalderon.DirichletFamily

/-- Exact pointwise packed model Green identity. Both the variable-frame
divergence cancellation and the genuine degree shift are included. -/
theorem model_covariant_green_point {Y : Set X} (hY : IsOpen Y)
    (d : Data) {K : ℝ} (hg : Elliptic Y K d.γ) (hK : 0 < K)
    (he : ∀ i,ContDiffOn ℝ ∞ (fun x => d.frame x i) Y)
    (hFrame : ∀ x ∈ Y,∀ i j,metricPair d.γ x (d.frame x i) (d.frame x j)=if i=j then 1 else 0)
    (Q : SmoothCoefficientJets 2)
    (hQ : ∀ z ∈ Metric.closedBall (0:X) 1,coefficientValue 2 Q =ᶠ[𝓝 z] (fun _ => (1:ℝ)))
    (U V : X → SphereSobolev 2) {y : X} (hy : y ∈ Y)
    (hU : DifferentiableAt ℝ U y) (hV : DifferentiableAt ℝ V y) :
    metricDensity d.γ y*(
      ⟪modelRaisingSection d U y,sphereSobolevInclusionL 1 0 (by norm_num)
        (sphereSobolevInclusionL 2 1 (by norm_num) (V y))⟫_ℝ-
      ⟪sphereSobolevInclusionL 1 0 (by norm_num) (sphereSobolevInclusionL 2 1 (by norm_num) (U y)),
        modelLoweringSection d V y-modelAdjointDefectSection d V y⟫_ℝ)=
      ∑ i : I,oneSectionCovariantVectorInnerDensity d (metricDensity d.γ)
        (fun x => sphereSobolevInclusionL 2 1 (by norm_num) (U x))
        (fun x => flatLoweringSobolevL 2 i (V x)) (fun x => d.frame x i) y := by
  let I21 := sphereSobolevInclusionL 2 1 (by norm_num)
  let I10 := sphereSobolevInclusionL 1 0 (by norm_num)
  have hCon := contracted_flat_lowering_covariant_pair hY d hg hK he hFrame V hy hV (I10 (I21 (U y)))
  have hAdj (i : I) :
      ⟪flatOneRaisingL i (highSectionCovariantDerivative d U y (d.frame y i)),I10 (I21 (V y))⟫_ℝ=
      ⟪oneSectionCovariantDerivative d (fun x => I21 (U x)) y (d.frame y i),
        I10 (flatLoweringSobolevL 2 i (V y))⟫_ℝ := by
    rw [oneSectionCovariantDerivative_high_inclusion d U y (d.frame y i) hU,
      flatLoweringSobolevL_two_coarse]
    exact flat_raising_lowering_inner Q hQ i _ _
  have hDegree (i : I) :
      ⟪flatOneRaisingL i (sphereSobolevShiftedDegreeL 2 (U y)),I10 (I21 (V y))⟫_ℝ=
      ⟪I10 (I21 (U y)),flatLoweringSobolevL 1 i (sphereSobolevShiftedDegreeL 2 (V y))-
        flatLoweringSobolevL 1 i (I21 (V y))⟫_ℝ := flat_raising_degree_inner Q hQ i _ _
  dsimp only [I10,I21] at hAdj hDegree hCon
  simp only [modelRaisingSection,modelLoweringSection,modelAdjointDefectSection,
    highSectionModelPlus,highSectionModelMinus,map_add,map_neg,map_smul,sum_inner,inner_sum,
    inner_add_left,inner_add_right,inner_sub_right,inner_neg_left,inner_neg_right,real_inner_smul_left,real_inner_smul_right,
    hAdj,hDegree,oneSectionCovariantVectorInnerDensity,Fin.sum_univ_three]
  simp only [Fin.sum_univ_three,flatOneLoweringL] at hCon
  unfold modelLogRadiusCoefficient
  linear_combination -hCon

end ShrinkingSpheres
