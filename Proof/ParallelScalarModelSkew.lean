import Proof.ParallelScalarModelAngularAdjunction
import Proof.FramedRaisingHalfEndpoints

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2800000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
open Set Filter
open scoped InnerProductSpace Topology
namespace ShrinkingSpheres.ParallelEnergy
open OAI.AnisotropicCalderon.SphereHarmonic OAI.AnisotropicCalderon.DirichletFamily

lemma framed_raising_degree_half_pair
    (Q : SmoothCoefficientJets 2)
    (hQ : ∀ z ∈ Metric.closedBall (0:X) 1,coefficientValue 2 Q =ᶠ[𝓝 z] (fun _ => (1:ℝ)))
    (d : Data) (y v : X) (u w : SphereSobolev (3/2:ℝ)) :
    sphereSobolevDualPairing (1/2:ℝ) (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num) u)
      (framedRaisingHalfL d y v (degreeHigherL w))=
    sphereSobolevDualPairing (1/2:ℝ) (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num) w)
      ((framedRaisingHalfL d y v).adjoint (degreeHigherL u-
        sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num) u)) := by
  simp only [framedRaisingHalfL,_root_.sum_apply,_root_.smul_apply,map_sum,map_smul,sphereSobolevDualPairing,inner_sum,inner_smul_right]
  exact Finset.sum_congr rfl (fun i _ => congrArg
    (fun r : ℝ => frameCoordinateLinear d.γ d.frame y i v*r)
    (flat_raising_degree_half_pair Q hQ i u w))

/-- A symmetric scalar contraction cancels the paired degree and
shifted-degree gradient terms before absolute values are taken. -/
theorem symmetric_raising_degree_gradient_cancel
    (Q : SmoothCoefficientJets 2)
    (hQ : ∀ z ∈ Metric.closedBall (0:X) 1,coefficientValue 2 Q =ᶠ[𝓝 z] (fun _ => (1:ℝ)))
    (d : Data) (y v : X) (q : I → I → ℝ) (hq : ∀ a b,q a b=q b a)
    (H : I → SphereSobolev (3/2:ℝ)) :
    (∑ a : I,∑ b : I,q a b*(
      sphereSobolevDualPairing (1/2:ℝ) (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num) (H b))
        (framedRaisingHalfL d y v (degreeHigherL (H a)))-
      sphereSobolevDualPairing (1/2:ℝ) (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num) (H b))
        ((framedRaisingHalfL d y v).adjoint (degreeHigherL (H a)-
          sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num) (H a)))))=0 := by
  let F := fun a b => sphereSobolevDualPairing (1/2:ℝ)
    (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num) (H b))
    ((framedRaisingHalfL d y v).adjoint (degreeHigherL (H a)-
      sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num) (H a)))
  have hp (a b : I) := framed_raising_degree_half_pair Q hQ d y v (H b) (H a)
  simp_rw [hp]
  change (∑ a : I,∑ b : I,q a b*(F b a-F a b))=0
  simp_rw [mul_sub,Finset.sum_sub_distrib]
  have hSwap : (∑ a : I,∑ b : I,q a b*F b a)=∑ a : I,∑ b : I,q a b*F a b := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => by rw [hq b a]))
  rw [hSwap,sub_self]

end ShrinkingSpheres.ParallelEnergy
