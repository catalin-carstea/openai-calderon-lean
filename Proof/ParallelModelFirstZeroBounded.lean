import Proof.ParallelModelFirstWordEndpoints
import Proof.ParallelScalarModelSkew
import Proof.ParallelModelFirstBoundedAlgebra

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2800000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set
open scoped InnerProductSpace
namespace ShrinkingSpheres.ParallelEnergy
open OAI.AnisotropicCalderon.SphereHarmonic

def modelFirstZeroBoundedResidual (d : Data) (b c : I) (y : X)
    (u5 : SphereSobolev (5/2:ℝ)) (h : SphereSobolev (3/2:ℝ)) : ℝ :=
  let Z := sphereSobolevInclusionL (1/2:ℝ) 0 (by norm_num);
  let u := sphereSobolevInclusionL (5/2:ℝ) (3/2:ℝ) (by norm_num) u5;
  ⟪Z (framedRaisingHigherL d y (axis c) (scalarModelDegreeSection (fun _ : X => u5) 0)),Z (modelFirstBoundedForwardHigh d b y h)⟫_ℝ-
    sphereSobolevDualPairing (1/2:ℝ) (effectiveFirstBoundedAdjointHigherL d b y u) (modelFirstZeroAdjointWeakL d c y h)

lemma model_first_zero_bounded_forward_pair
    (d : Data) (b c : I) (y : X) (u5 : SphereSobolev (5/2:ℝ)) (h : SphereSobolev (3/2:ℝ)) :
    ⟪sphereSobolevInclusionL (1/2:ℝ) 0 (by norm_num)
        (framedRaisingHigherL d y (axis c) (scalarModelDegreeSection (fun _ : X => u5) 0)),
      sphereSobolevInclusionL (1/2:ℝ) 0 (by norm_num) (modelFirstBoundedForwardHigh d b y h)⟫_ℝ=
      sphereSobolevDualPairing (1/2:ℝ) (modelFirstBoundedForwardHigh d b y h)
        (framedRaisingHalfL d y (axis c) (degreeHigherL (sphereSobolevInclusionL (5/2:ℝ) (3/2:ℝ) (by norm_num) u5))) := by
  have hM := DFunLike.congr_fun (framedRaisingHalf_balanced d y (axis c))
    (scalarModelDegreeSection (fun _ : X => u5) 0)
  simp only [ContinuousLinearMap.comp_apply,scalarModelDegreeSection_half_inclusion] at hM
  have hPair := half_dual_pairing_inclusion (modelFirstBoundedForwardHigh d b y h)
    (framedRaisingHigherL d y (axis c) (scalarModelDegreeSection (fun _ : X => u5) 0))
  rw [hM] at hPair
  exact (real_inner_comm _ _).trans hPair.symm

lemma model_first_zero_bounded_adjoint_pair
    (d : Data) (b c : I) (y : X) (u h : SphereSobolev (3/2:ℝ)) :
    sphereSobolevDualPairing (1/2:ℝ) (effectiveFirstBoundedAdjointHigherL d b y u)
      (modelFirstZeroAdjointWeakL d c y h)=
    sphereSobolevDualPairing (1/2:ℝ) (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num) h)
      (framedRaisingHalfL d y (axis c) (degreeHigherL (modelFirstBoundedAdjointThreeHalfL d b y u))) := by
  obtain ⟨Q,hQ⟩ := exists_unit_boundary_coefficient
  have hZ := DFunLike.congr_fun (modelFirstBoundedAdjointThreeHalfL_graph d b y) u
  have hSkew := framed_raising_degree_half_pair Q hQ d y (axis c) h (modelFirstBoundedAdjointThreeHalfL d b y u)
  simp only [ContinuousLinearMap.comp_apply] at hZ
  rw [hZ] at hSkew
  exact hSkew.symm

/-- The bounded geometric/scalar remainder is order zero at the SAME
half and reflected H3/2 grades. This controls both cubic orientations
without estimating an H3/2 horizontal derivative or H5/2 mass. -/
theorem model_first_zero_bounded_residual_bound
    (d : Data) (b c : I) (y : X) (u5 : SphereSobolev (5/2:ℝ)) (h : SphereSobolev (3/2:ℝ))
    (R0 CF CA ε β : ℝ) (hR0 : 0 ≤ R0) (hCF : 0 ≤ CF) (hCA : 0 ≤ CA) (hε : 0 ≤ ε) (hβ : 0 < β)
    (hR : ‖framedRaisingHalfL d y (axis c)‖ ≤ R0)
    (hF : ‖effectiveFirstBoundedRemainderAtL (1/2:ℝ) d b y‖ ≤ CF*ε/β^2)
    (hA : ‖modelFirstBoundedAdjointThreeHalfL d b y‖ ≤ CA*ε/β^2) :
    |modelFirstZeroBoundedResidual d b c y u5 h| ≤
      (2*R0*(CF+CA))*ε/β^2*
        ‖sphereSobolevInclusionL (5/2:ℝ) (3/2:ℝ) (by norm_num) u5‖*
        ‖sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num) h‖ := by
  have hG := model_first_bounded_zero_pair_norm (framedRaisingHalfL d y (axis c)) degreeHigherL
    (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num))
    (effectiveFirstBoundedRemainderAtL (1/2:ℝ) d b y) (modelFirstBoundedAdjointThreeHalfL d b y)
    (sphereSobolevInclusionL (5/2:ℝ) (3/2:ℝ) (by norm_num) u5) h R0 CF CA ε β
    hR0 hCF hCA hε hβ hR norm_degreeHigherL_le_two hF hA
  unfold modelFirstZeroBoundedResidual
  dsimp only
  rw [model_first_zero_bounded_forward_pair,model_first_zero_bounded_adjoint_pair]
  simpa only [modelFirstBoundedForwardHigh,ContinuousLinearMap.comp_apply] using hG

end ShrinkingSpheres.ParallelEnergy
