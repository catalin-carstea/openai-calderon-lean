import Proof.StrongHalfCovariantCalculus
import Proof.HalfCovariantDirectionLinear

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
open Set
open scoped ContDiff Topology
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.SphereHarmonic

/-- Strong extensions in orthonormal frame directions combine into one
in a fixed physical coordinate direction, with the same 3K norm factor. -/
lemma exists_strong_half_covariant_axis_extension {Y : Set X} (d : Data)
    {K : ℝ} (hg : Elliptic Y K d.γ) (hK : 1 ≤ K) {y : X} (hy : y ∈ Y)
    (hFrame : ∀ j k,metricPair d.γ y (d.frame y j) (d.frame y k)=if j=k then 1 else 0)
    (C : X → SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ)))
    (H : X → SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ))
    (L : I → SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ)))
    (hL : ∀ j,halfOperatorCovariantDerivativeL d C H y (d.frame y j)=
      (L j).comp (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)))
    (Q : ℝ) (hN : ∀ j,‖L j‖ ≤ Q) (i : I) :
    ∃ A : SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ)),
      halfOperatorCovariantDerivativeL d C H y (axis i)=
        A.comp (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)) ∧ ‖A‖ ≤ 3*K*Q := by
  let c := fun j => frameCoordinateLinear d.γ d.frame y j (axis i)
  let A := ∑ j : I,c j • L j
  have hMap := congrArg (halfOperatorCovariantDerivativeFamilyL d C H y)
    (frameCoordinateLinear_reconstruct d.γ d.frame y (axis i) hFrame)
  have hAxis : halfOperatorCovariantDerivativeL d C H y (axis i)=
      ∑ j : I,c j • halfOperatorCovariantDerivativeL d C H y (d.frame y j) := by
    simpa only [map_sum,map_smul,halfOperatorCovariantDerivativeFamilyL_apply] using hMap.symm
  refine ⟨A,?_,?_⟩
  · rw [hAxis]
    simp_rw [hL]
    apply ContinuousLinearMap.ext
    intro u
    simp only [A,ContinuousLinearMap.comp_apply,_root_.sum_apply,_root_.smul_apply]
  · exact norm_weighted_sum_three_le _ _ K Q (zero_le_one.trans hK)
      (fun j => by
        dsimp only [c]
        rw [frameCoordinateLinear_apply]
        exact hg.frame_coordinate_abs_bound hK d.frame hy hFrame i j) hN

end ShrinkingSpheres
