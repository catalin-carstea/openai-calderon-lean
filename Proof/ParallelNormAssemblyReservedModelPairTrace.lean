import Proof.ParallelScalarModelCoordinates
import Proof.ParallelNormAssemblyReservedModelLeadingIntegral

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
open OAI.AnisotropicCalderon.SphereHarmonic

def flatModelPotentialPairedFormL
    (C : SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ)))
    (u : SphereSobolev (3/2:ℝ)) (i : I) : SphereSobolev (3/2:ℝ) →L[ℝ] ℝ :=
  (innerSL ℝ (C u)).comp (flatThreeHalfRaisingL i)+
    (innerSL ℝ (flatThreeHalfRaisingL i u)).comp C

lemma flatModelPotentialPairedFormL_apply
    (C : SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ)))
    (u v : SphereSobolev (3/2:ℝ)) (i : I) :
    flatModelPotentialPairedFormL C u i v=
      sphereSobolevDualPairing (1/2:ℝ) (flatThreeHalfRaisingL i v) (C u)+
      sphereSobolevDualPairing (1/2:ℝ) (flatThreeHalfRaisingL i u) (C v) := by
  change ⟪C u,flatThreeHalfRaisingL i v⟫_ℝ+⟪flatThreeHalfRaisingL i u,C v⟫_ℝ=
    ⟪flatThreeHalfRaisingL i v,C u⟫_ℝ+⟪flatThreeHalfRaisingL i u,C v⟫_ℝ
  rw [real_inner_comm (C u)]

/-- Contract the paired leading term in the SAME orthonormal moving frame
before differentiating coefficients or estimating them. Thus no frame jet
is smuggled into the coordinate Green operation. -/
theorem model_potential_paired_frame_trace (d : Data) (y : X)
    (hFrame : ∀ i j,metricPair d.γ y (d.frame y i) (d.frame y j)=if i=j then 1 else 0)
    (C : SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ)))
    (u : SphereSobolev (3/2:ℝ)) (V : X →L[ℝ] SphereSobolev (3/2:ℝ)) :
    (∑ i : I,(sphereSobolevDualPairing (1/2:ℝ) (flatThreeHalfRaisingL i (V (d.frame y i))) (C u)+
      sphereSobolevDualPairing (1/2:ℝ) (flatThreeHalfRaisingL i u) (C (V (d.frame y i)))))=
    ∑ k : I,∑ c : I,(d.γ y)⁻¹ k c*(
      sphereSobolevDualPairing (1/2:ℝ) (framedRaisingHigherL d y (axis c) (V (axis k))) (C u)+
      sphereSobolevDualPairing (1/2:ℝ) (framedRaisingHigherL d y (axis c) u) (C (V (axis k)))) := by
  let L : X →L[ℝ] (SphereSobolev (3/2:ℝ) →L[ℝ] ℝ) :=
    ∑ j : I,(frameCoordinateLinear d.γ d.frame y j).smulRight (flatModelPotentialPairedFormL C u j)
  have hLF (i : I) : L (d.frame y i)=flatModelPotentialPairedFormL C u i := by
    simp only [L,_root_.sum_apply,ContinuousLinearMap.smulRight_apply,frameCoordinateLinear_apply,hFrame]
    simp
  have hLA (c : I) (v : SphereSobolev (3/2:ℝ)) :
      L (axis c) v=sphereSobolevDualPairing (1/2:ℝ) (framedRaisingHigherL d y (axis c) v) (C u)+
        sphereSobolevDualPairing (1/2:ℝ) (framedRaisingHigherL d y (axis c) u) (C v) := by
    simp only [L,_root_.sum_apply,ContinuousLinearMap.smulRight_apply,_root_.smul_apply,
      flatModelPotentialPairedFormL_apply,framedRaisingHigherL,map_sum,map_smul,
      sphereSobolevDualPairing,inner_sum,inner_smul_left,sum_inner,real_inner_smul_left,
      Finset.sum_add_distrib,smul_eq_mul]
    simp [mul_add,Finset.sum_add_distrib]
  have hTrace := scalar_model_linear_frame_trace d.γ d.frame y hFrame L V
  calc
    _ = ∑ i : I,L (d.frame y i) (V (d.frame y i)) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [hLF,flatModelPotentialPairedFormL_apply]
    _ = _ := hTrace.trans (by simp only [hLA,smul_eq_mul])

lemma five_half_covariant_derivative_reserved_eq (d : Data)
    (U : X → SphereSobolev (5/2:ℝ)) (y a : X) :
    fiveHalfCovariantDerivative d U a y=fiveHalfSectionCovariantDerivativeL d U y a := by
  exact graded_covariant_derivative_five_half d U y a

end ShrinkingSpheres.ParallelEnergy
