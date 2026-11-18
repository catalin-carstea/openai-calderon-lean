import Proof.ParallelNormAssemblyReservedModelWords
import Proof.ParallelNormAssemblyReservedCubicCorePair
import Proof.ParallelScalarModelWeakSections

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2800000
set_option maxRecDepth 10000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter
open scoped ContDiff Topology InnerProductSpace
namespace ShrinkingSpheres.ParallelEnergy
open OAI.AnisotropicCalderon.SphereHarmonic OAI.AnisotropicCalderon.DirichletFamily

lemma quadratic_word_adjoint_core_balanced {Y : Set X} {d : Data} {CF CT CG CK : ℝ}
    (P : PhysicalPrincipalData Y d CF CT) {y : X} (W : PhysicalPotentialQuarticData P y CG CK)
    (p : PhysicalPotentialGeneratorIndex → PhysicalPotentialGeneratorIndex → ℝ)
    (u : SphereSobolev (3/2:ℝ)) (v : PhysicalPotentialGeneratorIndex → SphereSobolev (3/2:ℝ))
    (hv : ∀ c,sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num) (v c)=W.adjointHigh c u) :
    sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)
      (quadraticWordAdjointCoreValue P W p v)=quadraticWordAdjointWeakValue P W p u := by
  simp only [quadraticWordAdjointCoreValue,quadraticWordAdjointWeakValue,map_sum,map_smul]
  apply Finset.sum_congr rfl
  intro c _
  apply Finset.sum_congr rfl
  intro e _
  apply congrArg (fun z => p c e • z)
  have h := DFunLike.congr_fun (W.adjoint_compatible e) (v c)
  simp only [ContinuousLinearMap.comp_apply] at h
  exact h.trans (congrArg (P.potentialGeneratorLow y e).adjoint (hv c))

/-- The model's degree-minus-one term is exactly the true adjoint of its
raising/degree word, on genuine H3/2 arguments and the same W. -/
lemma model_zero_weak_adjoint_identity {Y : Set X} {d : Data} {CF CT CG CK : ℝ}
    (P : PhysicalPrincipalData Y d CF CT) {y : X} (hy : y ∈ Y)
    (W : PhysicalPotentialQuarticData P y CG CK)
    (Q : SmoothCoefficientJets 2)
    (hQ : ∀ z ∈ Metric.closedBall (0:X) 1,coefficientValue 2 Q =ᶠ[𝓝 z] (fun _ => (1:ℝ)))
    (u : SphereSobolev (3/2:ℝ)) :
    quadraticWordAdjointWeakValue P W (modelZeroWordCoefficient d y) u=
      ∑ i : I,modelLogRadiusCoefficient d i y • (flatHalfRaisingL i).adjoint
        (degreeHigherL u-sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num) u) := by
  apply (denseRange_sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)).eq_of_inner_right ℝ
  intro v
  change sphereSobolevDualPairing (1/2:ℝ)
    (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num) v) _=_
  rw [quadratic_word_weak_adjunction P hy W]
  simp only [quadraticWordForwardWeakValue,modelZeroWordCoefficient,Fintype.sum_sum_type,Fintype.sum_unique,
    zero_smul,Finset.sum_const_zero,zero_add,add_zero,PhysicalPrincipalData.potentialGeneratorLow,
    PhysicalPrincipalData.potentialGeneratorHigh,degreeHigherL,sphereSobolevDualPairing,
    inner_sum,inner_smul_right]
  apply Finset.sum_congr rfl
  intro i _
  exact congrArg (fun t => modelLogRadiusCoefficient d i y*t) (flat_raising_degree_half_pair Q hQ i u v)

/-- Actual model-zero adjoint on the H5/2 core, retaining the genuine
lowering degree-minus-one term. No chosen higher endpoint is replaced. -/
theorem model_zero_adjoint_actual {Y : Set X} {d : Data} {CF CT CG CK : ℝ}
    (P : PhysicalPrincipalData Y d CF CT) {y : X} (hy : y ∈ Y)
    (W : PhysicalPotentialQuarticData P y CG CK)
    (Q : SmoothCoefficientJets 2)
    (hQ : ∀ z ∈ Metric.closedBall (0:X) 1,coefficientValue 2 Q =ᶠ[𝓝 z] (fun _ => (1:ℝ)))
    (u : SphereSobolev (5/2:ℝ)) :
    modelZeroAdjointCoreValue P W u=
      ∑ i : I,modelLogRadiusCoefficient d i y • flatLoweringSobolevL 1 i
        (sphereSobolevShiftedDegreeL 2 (sphereSobolevInclusionL (5/2:ℝ) 2 (by norm_num) u)-
          sphereSobolevInclusionL (5/2:ℝ) 1 (by norm_num) u) := by
  apply sphereSobolevInclusionL_injective 0 (-(1/2:ℝ)) (by norm_num)
  have hCore := quadratic_word_adjoint_core_balanced P W (modelZeroWordCoefficient d y)
    (sphereSobolevInclusionL (5/2:ℝ) (3/2:ℝ) (by norm_num) u)
    (fun c => W.reverseFirstWordHigherL c u) (fun c => W.reverseFirstWordHigherL_inclusion c u)
  have hWeak := model_zero_weak_adjoint_identity P hy W Q hQ
    (sphereSobolevInclusionL (5/2:ℝ) (3/2:ℝ) (by norm_num) u)
  simp only [modelZeroAdjointCoreValue,sphereSobolevInclusionL_trans_apply]
  rw [hCore,hWeak,map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [map_smul]
  apply congrArg (fun z => modelLogRadiusCoefficient d i y • z)
  have hAdj := DFunLike.congr_fun (flat_lowering_coarse_half_graph Q hQ i)
    (sphereSobolevShiftedDegreeL 2 (sphereSobolevInclusionL (5/2:ℝ) 2 (by norm_num) u)-
      sphereSobolevInclusionL (5/2:ℝ) 1 (by norm_num) u)
  simp only [ContinuousLinearMap.comp_apply] at hAdj
  apply Eq.trans ?_ hAdj.symm
  apply congrArg (flatHalfRaisingL i).adjoint
  simp only [map_sub,sphereSobolevInclusionL_trans_apply]
  congr 1
  have hh := scalar_model_degree_coarse_half (fun _ : X => u) y
  simpa only [fiveHalfToTwoSection] using hh.symm

end ShrinkingSpheres.ParallelEnergy
