import Proof.FlatLoweringSobolev
import Proof.FrameErrorMatrixRaisingCross
import Proof.FlatLoweringSectionCalculus
import Proof.DegreeAdjointHigherEndpoint
import Proof.HalfScalarTransposeCompatibility

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2800000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter
open scoped InnerProductSpace Topology
namespace ShrinkingSpheres.ParallelEnergy
open OAI.AnisotropicCalderon.SphereHarmonic OAI.AnisotropicCalderon.DirichletFamily
open OAI.AnisotropicCalderon.NativeHarmonicHalfCoarseDualPairing

/-- A genuine coarse adjoint pair determines the true low half adjoint
through dense inclusions, without identifying Sobolev carrier orders. -/
lemma scalar_model_coarse_half_adjoint_graph
    (B Ba : SphereSobolev 1 →L[ℝ] SphereSobolev 0)
    (C : SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ)))
    (hB : (sphereSobolevInclusionL 0 (-(1/2:ℝ)) (by norm_num)).comp B=
      C.comp (sphereSobolevInclusionL 1 (1/2:ℝ) (by norm_num)))
    (hPair : ∀ u v : SphereSobolev 1,⟪B u,sphereSobolevInclusionL 1 0 (by norm_num) v⟫_ℝ=
      ⟪sphereSobolevInclusionL 1 0 (by norm_num) u,Ba v⟫_ℝ) :
    (sphereSobolevInclusionL 0 (-(1/2:ℝ)) (by norm_num)).comp Ba=
      C.adjoint.comp (sphereSobolevInclusionL 1 (1/2:ℝ) (by norm_num)) := by
  apply ContinuousLinearMap.ext
  intro v
  apply (denseRange_sphereSobolevInclusionL 1 (1/2:ℝ) (by norm_num)).eq_of_inner_right ℝ
  intro u
  have hBu := DFunLike.congr_fun hB u
  simp only [ContinuousLinearMap.comp_apply] at hBu ⊢
  change sphereSobolevDualPairing (1/2:ℝ) _ _=_
  rw [sphereSobolevDualPairing_zero_inclusion (1/2:ℝ) (by norm_num),sphereSobolevInclusionL_trans_apply]
  calc
    _ = ⟪B u,sphereSobolevInclusionL 1 0 (by norm_num) v⟫_ℝ := (hPair u v).symm
    _ = sphereSobolevDualPairing (1/2:ℝ) (sphereSobolevInclusionL 1 (1/2:ℝ) (by norm_num) v)
        (sphereSobolevInclusionL 0 (-(1/2:ℝ)) (by norm_num) (B u)) := by
      rw [sphereSobolevDualPairing_zero_inclusion (1/2:ℝ) (by norm_num),sphereSobolevInclusionL_trans_apply,real_inner_comm]
    _ = _ := by
      rw [hBu,C.adjoint_inner_right]
      exact real_inner_comm _ _

lemma flat_lowering_coarse_half_graph
    (Q : SmoothCoefficientJets 2)
    (hQ : ∀ z ∈ Metric.closedBall (0:X) 1,coefficientValue 2 Q =ᶠ[𝓝 z] (fun _ => (1:ℝ))) (i : I) :
    (sphereSobolevInclusionL 0 (-(1/2:ℝ)) (by norm_num)).comp (flatLoweringSobolevL 1 i)=
      (flatHalfRaisingL i).adjoint.comp (sphereSobolevInclusionL 1 (1/2:ℝ) (by norm_num)) := by
  apply scalar_model_coarse_half_adjoint_graph (flatRaisingSobolevL 1 i) (flatLoweringSobolevL 1 i)
    (flatHalfRaisingL i) ?_ (flat_raising_lowering_inner Q hQ i)
  apply ContinuousLinearMap.ext
  intro u
  exact flatOneRaisingL_half i u

lemma scalar_model_half_pair_coarse_value
    (B : SphereSobolev 1 →L[ℝ] SphereSobolev 0)
    (C : SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ)))
    (hB : (sphereSobolevInclusionL 0 (-(1/2:ℝ)) (by norm_num)).comp B=
      C.comp (sphereSobolevInclusionL 1 (1/2:ℝ) (by norm_num)))
    (u : SphereSobolev (3/2:ℝ)) (v : SphereSobolev 1) :
    sphereSobolevDualPairing (1/2:ℝ) (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num) u)
      (C (sphereSobolevInclusionL 1 (1/2:ℝ) (by norm_num) v))=
    ⟪sphereSobolevInclusionL (3/2:ℝ) 0 (by norm_num) u,B v⟫_ℝ := by
  have h := DFunLike.congr_fun hB v
  simp only [ContinuousLinearMap.comp_apply] at h
  rw [← h,sphereSobolevDualPairing_zero_inclusion (1/2:ℝ) (by norm_num),sphereSobolevInclusionL_trans_apply]

/-- The exact model zeroth angular terms form a skew bilinear pair. The
degree-minus-one shift is retained, rather than estimated separately. -/
theorem flat_raising_degree_half_pair
    (Q : SmoothCoefficientJets 2)
    (hQ : ∀ z ∈ Metric.closedBall (0:X) 1,coefficientValue 2 Q =ᶠ[𝓝 z] (fun _ => (1:ℝ)))
    (i : I) (u v : SphereSobolev (3/2:ℝ)) :
    sphereSobolevDualPairing (1/2:ℝ) (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num) u)
      (flatHalfRaisingL i (degreeHigherL v))=
    sphereSobolevDualPairing (1/2:ℝ) (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num) v)
      ((flatHalfRaisingL i).adjoint (degreeHigherL u-
        sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num) u)) := by
  have hForward : (sphereSobolevInclusionL 0 (-(1/2:ℝ)) (by norm_num)).comp (flatRaisingSobolevL 1 i)=
      (flatHalfRaisingL i).comp (sphereSobolevInclusionL 1 (1/2:ℝ) (by norm_num)) :=
    ContinuousLinearMap.ext (flatOneRaisingL_half i)
  have hAdj := flat_lowering_coarse_half_graph Q hQ i
  have hDeg (z : SphereSobolev 2) : degreeHigherL (sphereSobolevInclusionL 2 (3/2:ℝ) (by norm_num) z)=
      sphereSobolevInclusionL 1 (1/2:ℝ) (by norm_num) (sphereSobolevShiftedDegreeL 2 z) := by
    have h := sphereSobolevShiftedDegreeL_inclusion 2 (3/2:ℝ) (by norm_num) z
    have hI : sphereSobolevInclusionL ((2:ℝ)-1) ((3/2:ℝ)-1) (by norm_num)=
        sphereSobolevInclusionL 1 (1/2:ℝ) (by norm_num) := by congr 1 <;> norm_num
    simpa only [degreeHigherL,hI] using h.symm
  have hCore (a b : SphereSobolev 2) :
      sphereSobolevDualPairing (1/2:ℝ)
        (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num) (sphereSobolevInclusionL 2 (3/2:ℝ) (by norm_num) a))
        (flatHalfRaisingL i (degreeHigherL (sphereSobolevInclusionL 2 (3/2:ℝ) (by norm_num) b)))=
      sphereSobolevDualPairing (1/2:ℝ)
        (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num) (sphereSobolevInclusionL 2 (3/2:ℝ) (by norm_num) b))
        ((flatHalfRaisingL i).adjoint (degreeHigherL (sphereSobolevInclusionL 2 (3/2:ℝ) (by norm_num) a)-
          sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num) (sphereSobolevInclusionL 2 (3/2:ℝ) (by norm_num) a))) := by
    rw [hDeg a,hDeg b]
    have hMinus : sphereSobolevInclusionL 1 (1/2:ℝ) (by norm_num) (sphereSobolevShiftedDegreeL 2 a)-
        sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num) (sphereSobolevInclusionL 2 (3/2:ℝ) (by norm_num) a)=
        sphereSobolevInclusionL 1 (1/2:ℝ) (by norm_num)
          (sphereSobolevShiftedDegreeL 2 a-sphereSobolevInclusionL 2 1 (by norm_num) a) := by
      simp only [map_sub,sphereSobolevInclusionL_trans_apply]
    rw [hMinus]
    have hp := scalar_model_half_pair_coarse_value (flatRaisingSobolevL 1 i) (flatHalfRaisingL i) hForward
      (sphereSobolevInclusionL 2 (3/2:ℝ) (by norm_num) a) (sphereSobolevShiftedDegreeL 2 b)
    have hm := scalar_model_half_pair_coarse_value (flatLoweringSobolevL 1 i) (flatHalfRaisingL i).adjoint hAdj
      (sphereSobolevInclusionL 2 (3/2:ℝ) (by norm_num) b)
      (sphereSobolevShiftedDegreeL 2 a-sphereSobolevInclusionL 2 1 (by norm_num) a)
    simp only [sphereSobolevInclusionL_trans_apply,map_sub] at hp hm ⊢
    have hh : ⟪flatRaisingSobolevL 1 i (sphereSobolevShiftedDegreeL 2 b),
        sphereSobolevInclusionL 2 0 (by norm_num) a⟫_ℝ=
        ⟪sphereSobolevInclusionL 2 0 (by norm_num) b,
          flatLoweringSobolevL 1 i (sphereSobolevShiftedDegreeL 2 a)-
            flatLoweringSobolevL 1 i (sphereSobolevInclusionL 2 1 (by norm_num) a)⟫_ℝ := by
      simpa only [flatOneLoweringL,sphereSobolevInclusionL_trans_apply] using flat_raising_degree_inner Q hQ i b a
    exact hp.trans ((real_inner_comm _ _).trans (hh.trans hm.symm))
  exact (denseRange_sphereSobolevInclusionL 2 (3/2:ℝ) (by norm_num)).induction_on₂
    (isClosed_eq (by dsimp only [sphereSobolevDualPairing];fun_prop)
      (by dsimp only [sphereSobolevDualPairing];fun_prop)) hCore u v

end ShrinkingSpheres.ParallelEnergy
