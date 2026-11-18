import Proof.ParallelScalarModelDegreeSections
import Proof.ParallelScalarModelSkew

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

lemma half_pair_adjoint_swap
    (C : SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ)))
    (u v : SphereSobolev (1/2:ℝ)) :
    sphereSobolevDualPairing (1/2:ℝ) u (C v)=
      sphereSobolevDualPairing (1/2:ℝ) v (C.adjoint u) := by
  change ⟪u,C v⟫_ℝ=⟪v,C.adjoint u⟫_ℝ
  rw [C.adjoint_inner_right,real_inner_comm]

theorem scalar_model_degree_section_gradient_cancel
    (Q : SmoothCoefficientJets 2)
    (hQ : ∀ z ∈ Metric.closedBall (0:X) 1,coefficientValue 2 Q =ᶠ[𝓝 z] (fun _ => (1:ℝ)))
    (d : Data) (U : X → SphereSobolev (5/2:ℝ)) (y : X) (hU : DifferentiableAt ℝ U y)
    (q : I → I → ℝ) (hSym : ∀ a b,q a b=q b a) (c : I) :
    (∑ a : I,∑ b : I,q a b*(
      sphereSobolevDualPairing (1/2:ℝ) (halfSectionCovariantDerivativeL d (scalarModelDegreeSection U) y (axis a))
        ((framedRaisingHalfL d y (axis c)).adjoint (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)
          (fiveHalfCovariantDerivative d U (axis b) y)))-
      sphereSobolevDualPairing (1/2:ℝ) (halfSectionCovariantDerivativeL d (scalarModelShiftedDegreeSection U) y (axis a))
        (framedRaisingHalfL d y (axis c) (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)
          (fiveHalfCovariantDerivative d U (axis b) y)))))=0 := by
  let J := sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)
  let H := fun a : I => fiveHalfCovariantDerivative d U (axis a) y
  let R := framedRaisingHalfL d y (axis c)
  have h0 (a b : I) :
      sphereSobolevDualPairing (1/2:ℝ) (halfSectionCovariantDerivativeL d (scalarModelDegreeSection U) y (axis a))
        (R.adjoint (J (H b)))=
      sphereSobolevDualPairing (1/2:ℝ) (J (H b)) (R (degreeHigherL (H a))) := by
    have hd := scalarModelDegreeSection_covariant_derivative d U y (axis a) hU
    have hp := congrArg (fun z : SphereSobolev (1/2:ℝ) => sphereSobolevDualPairing (1/2:ℝ) z (R.adjoint (J (H b)))) hd
    have hs : sphereSobolevDualPairing (1/2:ℝ) (degreeHigherL (H a)) (R.adjoint (J (H b)))=
        sphereSobolevDualPairing (1/2:ℝ) (J (H b)) (R (degreeHigherL (H a))) := by
      simpa only [ContinuousLinearMap.adjoint_adjoint] using half_pair_adjoint_swap R.adjoint (degreeHigherL (H a)) (J (H b))
    exact hp.trans hs
  have h1 (a b : I) :
      sphereSobolevDualPairing (1/2:ℝ) (halfSectionCovariantDerivativeL d (scalarModelShiftedDegreeSection U) y (axis a))
        (R (J (H b)))=
      sphereSobolevDualPairing (1/2:ℝ) (J (H b)) (R.adjoint (degreeHigherL (H a)-J (H a))) := by
    have hd := scalarModelShiftedDegreeSection_covariant_derivative d U y (axis a) hU
    have hp := congrArg (fun z : SphereSobolev (1/2:ℝ) => sphereSobolevDualPairing (1/2:ℝ) z (R (J (H b)))) hd
    exact hp.trans (half_pair_adjoint_swap R (degreeHigherL (H a)-J (H a)) (J (H b)))
  have hCancel := symmetric_raising_degree_gradient_cancel Q hQ d y (axis c) q hSym H
  apply Eq.trans _ hCancel
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  exact congrArg (fun r : ℝ => q a b*r) (congrArg₂ (fun r s : ℝ => r-s) (h0 a b) (h1 a b))

end ShrinkingSpheres.ParallelEnergy
