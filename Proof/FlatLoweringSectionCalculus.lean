import Proof.CanonicalLoweringCovariantGraph
import Proof.CovariantTensorSectionApplication
import Proof.ActualFrameErrorLift

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set
open scoped ContDiff Topology InnerProductSpace
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.SphereHarmonic
open OAI.AnisotropicCalderon.DirichletFamily

lemma flatLoweringSobolevL_two_coarse (i : I) (u : SphereSobolev 2) :
    sphereSobolevInclusionL 1 0 (by norm_num) (flatLoweringSobolevL 2 i u)=
      flatOneLoweringL i (sphereSobolevInclusionL 2 1 (by norm_num) u) := by
  have hI : sphereSobolevInclusionL ((2:ℝ)-1) ((1:ℝ)-1) (by norm_num)=
      sphereSobolevInclusionL 1 0 (by norm_num) := by congr 1 <;> norm_num
  have hh := flatLoweringSobolevL_inclusion 2 1 (by norm_num) i
  rw [hI] at hh
  exact (DFunLike.congr_fun hh u).symm

lemma oneSectionCovariantDerivative_flatLowering (d : Data) (U : X → SphereSobolev 2)
    (y a : X) (hU : DifferentiableAt ℝ U y)
    (hSkew : ∀ p q,frameConnectionCoefficient d.γ d.frame y a p q=
      -frameConnectionCoefficient d.γ d.frame y a q p) (i : I) :
    oneSectionCovariantDerivative d (fun x => flatLoweringSobolevL 2 i (U x)) y a=
      (∑ k : I,frameConnectionCoefficient d.γ d.frame y a i k •
        flatOneLoweringL k (sphereSobolevInclusionL 2 1 (by norm_num) (U y)))+
      flatOneLoweringL i (highSectionCovariantDerivative d U y a) := by
  have hh := (flatOneLoweringL_covariant_graph d y a hSkew i).apply_oneSection
    (differentiableAt_const _) U hU (fun x => flatLoweringSobolevL 2 i (U x))
    ((flatLoweringSobolevL 2 i).differentiableAt.comp y hU)
    (Filter.Eventually.of_forall (fun x => flatLoweringSobolevL_two_coarse i (U x)))
  simpa only [_root_.sum_apply,_root_.smul_apply] using hh

/-- The model zero term's genuine degree transposition produces exactly
one lowering operator, the manuscript model-adjoint defect. -/
lemma flat_raising_degree_inner (Q : SmoothCoefficientJets 2)
    (hQ : ∀ z ∈ Metric.closedBall (0:X) 1,coefficientValue 2 Q =ᶠ[𝓝 z] (fun _ => (1:ℝ)))
    (i : I) (u v : SphereSobolev 2) :
    ⟪flatRaisingSobolevL 1 i (sphereSobolevShiftedDegreeL 2 u),
      sphereSobolevInclusionL 1 0 (by norm_num) (sphereSobolevInclusionL 2 1 (by norm_num) v)⟫_ℝ=
    ⟪sphereSobolevInclusionL 1 0 (by norm_num) (sphereSobolevInclusionL 2 1 (by norm_num) u),
      flatOneLoweringL i (sphereSobolevShiftedDegreeL 2 v)-
        flatOneLoweringL i (sphereSobolevInclusionL 2 1 (by norm_num) v)⟫_ℝ := by
  have hComm := degree_flatLoweringSobolev_commutator 2 i
  have hL : flatLoweringSobolevL ((2:ℝ)-1) i=flatOneLoweringL i := by
    change flatLoweringSobolevL ((2:ℝ)-1) i=flatLoweringSobolevL 1 i
    rw [show (2:ℝ)-1=1 by norm_num]
  have hD : sphereSobolevShiftedDegreeL ((2:ℝ)-1)=sphereSobolevDegreeL := by
    rw [show (2:ℝ)-1=1 by norm_num,sphereSobolevShiftedDegreeL_one_eq_degree]
  have hI : sphereSobolevInclusionL ((2:ℝ)-1) (((2:ℝ)-1)-1) (by norm_num)=
      sphereSobolevInclusionL 1 0 (by norm_num) := by congr 1 <;> norm_num
  rw [hL,hD,hI] at hComm
  have hPoint := DFunLike.congr_fun hComm v
  simp only [_root_.sub_apply,ContinuousLinearMap.comp_apply,_root_.neg_apply,
    flatLoweringSobolevL_two_coarse] at hPoint
  have hB : sphereSobolevDegreeL (flatLoweringSobolevL 2 i v)=
      flatOneLoweringL i (sphereSobolevShiftedDegreeL 2 v)-
        flatOneLoweringL i (sphereSobolevInclusionL 2 1 (by norm_num) v) := by
    exact (sub_eq_iff_eq_add.mp hPoint).trans (by abel)
  calc
    _ = ⟪sphereSobolevInclusionL 1 0 (by norm_num) (sphereSobolevShiftedDegreeL 2 u),
        flatOneLoweringL i (sphereSobolevInclusionL 2 1 (by norm_num) v)⟫_ℝ :=
      flat_raising_lowering_inner Q hQ i _ _
    _ = ⟪sphereSobolevDegreeL (sphereSobolevInclusionL 2 1 (by norm_num) u),
        sphereSobolevInclusionL 1 0 (by norm_num) (flatLoweringSobolevL 2 i v)⟫_ℝ :=
      congrArg₂ (fun x y : SphereSobolev 0 => ⟪x,y⟫_ℝ)
        (sphereSobolevShiftedDegreeL_two_coarse u) (flatLoweringSobolevL_two_coarse i v).symm
    _ = ⟪sphereSobolevInclusionL 1 0 (by norm_num) (sphereSobolevInclusionL 2 1 (by norm_num) u),
        sphereSobolevDegreeL (flatLoweringSobolevL 2 i v)⟫_ℝ := sphereSobolevDegreeL_symmetric _ _
    _ = _ := congrArg (fun z : SphereSobolev 0 =>
      ⟪sphereSobolevInclusionL 1 0 (by norm_num) (sphereSobolevInclusionL 2 1 (by norm_num) u),z⟫_ℝ) hB

end ShrinkingSpheres
