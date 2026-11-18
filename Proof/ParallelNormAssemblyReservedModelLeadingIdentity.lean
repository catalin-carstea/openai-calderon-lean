import Proof.ParallelNormAssemblyReservedCubicCorePair
import Proof.ParallelScalarModelWeakSections

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2800000
set_option maxRecDepth 10000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set
open scoped ContDiff Topology InnerProductSpace
namespace ShrinkingSpheres.ParallelEnergy
open OAI.AnisotropicCalderon.SphereHarmonic OAI.AnisotropicCalderon.DirichletFamily
open OAI.AnisotropicCalderon.NativeHarmonicHalfCoarseDualPairing

lemma flat_raising_higher_coarse (i : I) (h : SphereSobolev (3/2:ℝ)) :
    sphereSobolevInclusionL (1/2:ℝ) 0 (by norm_num) (flatThreeHalfRaisingL i h)=
      flatRaisingSobolevL 1 i (sphereSobolevInclusionL (3/2:ℝ) 1 (by norm_num) h) := by
  have hI : sphereSobolevInclusionL ((3/2:ℝ)-1) ((1:ℝ)-1) (by norm_num)=
      sphereSobolevInclusionL (1/2:ℝ) 0 (by norm_num) := by congr 1 <;> norm_num
  have hh := DFunLike.congr_fun (flatRaisingSobolevL_inclusion (3/2:ℝ) 1 (by norm_num) i) h
  simpa only [ContinuousLinearMap.comp_apply,hI,flatThreeHalfRaisingL] using hh.symm

lemma flat_lowering_higher_coarse {Y : Set X} {d : Data} {CF CT CG CK : ℝ}
    (P : PhysicalPrincipalData Y d CF CT) {y : X} (W : PhysicalPotentialQuarticData P y CG CK)
    (Q : SmoothCoefficientJets 2)
    (hQ : ∀ z ∈ Metric.closedBall (0:X) 1,coefficientValue 2 Q =ᶠ[𝓝 z] (fun _ => (1:ℝ)))
    (i : I) (h : SphereSobolev (3/2:ℝ)) :
    sphereSobolevInclusionL (1/2:ℝ) 0 (by norm_num) (W.adjointHigh (.inr (.inl i)) h)=
      flatLoweringSobolevL 1 i (sphereSobolevInclusionL (3/2:ℝ) 1 (by norm_num) h) := by
  apply sphereSobolevInclusionL_injective 0 (-(1/2:ℝ)) (by norm_num)
  have hA := DFunLike.congr_fun (W.adjoint_compatible (.inr (.inl i))) h
  have hL := DFunLike.congr_fun (flat_lowering_coarse_half_graph Q hQ i)
    (sphereSobolevInclusionL (3/2:ℝ) 1 (by norm_num) h)
  simp only [ContinuousLinearMap.comp_apply,sphereSobolevInclusionL_trans_apply] at hA hL ⊢
  exact hA.trans hL.symm

/-- BOTH literal model-leading/potential orientations are combined before
norms. The unwanted angular horizontal order cancels into the weak Green
partner and a transposed genuine cubic commutator. -/
theorem flat_model_potential_leading_pair {Y : Set X} {d : Data} {CF CT CG CK : ℝ}
    (P : PhysicalPrincipalData Y d CF CT) {y : X} (hy : y ∈ Y)
    (W : PhysicalPotentialQuarticData P y CG CK)
    (Q : SmoothCoefficientJets 2)
    (hQ : ∀ z ∈ Metric.closedBall (0:X) 1,coefficientValue 2 Q =ᶠ[𝓝 z] (fun _ => (1:ℝ)))
    (i : I) (u : SphereSobolev (5/2:ℝ)) (h : SphereSobolev (3/2:ℝ)) :
    ⟪flatRaisingSobolevL 1 i (sphereSobolevInclusionL (3/2:ℝ) 1 (by norm_num) h),P.potentialQuadraticCoreL W u⟫_ℝ+
      ⟪flatLoweringSobolevL 1 i (sphereSobolevInclusionL (3/2:ℝ) 1 (by norm_num) h),P.potentialQuadraticAdjointCoreL W u⟫_ℝ=
      sphereSobolevDualPairing (1/2:ℝ) (flatThreeHalfRaisingL i h)
        (P.potentialQuadraticHalfL y (sphereSobolevInclusionL (5/2:ℝ) (3/2:ℝ) (by norm_num) u))+
      sphereSobolevDualPairing (1/2:ℝ)
        (flatThreeHalfRaisingL i (sphereSobolevInclusionL (5/2:ℝ) (3/2:ℝ) (by norm_num) u))
        (P.potentialQuadraticHalfL y h)-
      sphereSobolevDualPairing (1/2:ℝ) (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num) h)
        (cubicWordAdjointCommutatorValue P W (.inr (.inl i)) (PhysicalPrincipalData.potentialWordCoefficient d y)
          (sphereSobolevInclusionL (5/2:ℝ) (3/2:ℝ) (by norm_num) u)) := by
  have hForward : ⟪flatRaisingSobolevL 1 i (sphereSobolevInclusionL (3/2:ℝ) 1 (by norm_num) h),P.potentialQuadraticCoreL W u⟫_ℝ=
      sphereSobolevDualPairing (1/2:ℝ) (flatThreeHalfRaisingL i h)
        (P.potentialQuadraticHalfL y (sphereSobolevInclusionL (5/2:ℝ) (3/2:ℝ) (by norm_num) u)) := by
    rw [←P.potentialQuadraticCoreL_balanced hy W u,
      sphereSobolevDualPairing_zero_inclusion (1/2:ℝ) (by norm_num),flat_raising_higher_coarse]
  have hAdj := adjoint_generator_quadratic_core_pair P hy W (.inr (.inl i))
    (PhysicalPrincipalData.potentialWordCoefficient d y)
    (sphereSobolevInclusionL (5/2:ℝ) (3/2:ℝ) (by norm_num) u) h
    (fun b => W.forwardFirstWordHigherL b u) (fun b => W.reverseFirstWordHigherL b u)
    (fun b => W.forwardFirstWordHigherL_inclusion hy b u) (fun b => W.reverseFirstWordHigherL_inclusion b u)
  have hQW : quadraticWordForwardWeakValue P y (PhysicalPrincipalData.potentialWordCoefficient d y) h=
      P.potentialQuadraticHalfL y h := by
    rw [P.potentialQuadraticHalfL_eq_word_matrix]
    simp only [quadraticWordForwardWeakValue,PhysicalPrincipalData.potentialWordMatrixL,_root_.sum_apply,_root_.smul_apply,
      ContinuousLinearMap.comp_apply]
  have hQC : P.potentialQuadraticAdjointCoreL W u=
      sphereSobolevInclusionL (1/2:ℝ) 0 (by norm_num)
        (quadraticWordAdjointCoreValue P W (PhysicalPrincipalData.potentialWordCoefficient d y)
          (fun b => W.reverseFirstWordHigherL b u)) := by
    simp only [PhysicalPrincipalData.potentialQuadraticAdjointCoreL,quadraticWordAdjointCoreValue,
      ContinuousLinearMap.comp_apply,_root_.sum_apply,_root_.smul_apply]
  rw [flat_lowering_higher_coarse P W Q hQ i h,←hQC,hQW] at hAdj
  simp only [PhysicalPrincipalData.potentialGeneratorHigh] at hAdj
  rw [hForward,hAdj]
  ring

end ShrinkingSpheres.ParallelEnergy
