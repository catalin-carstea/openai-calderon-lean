import Proof.ParallelScalarModelCoordinates
import Proof.ParallelScalarModelWeakSections

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2800000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
open Set Filter
open scoped ContDiff Topology InnerProductSpace
namespace ShrinkingSpheres.ParallelEnergy
open OAI.AnisotropicCalderon.SphereHarmonic

def scalarModelLoweringDirectionalLinear (d : Data) (y : X) :
    X →L[ℝ] (SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ))) :=
  ∑ j : I,(frameCoordinateLinear d.γ d.frame y j).smulRight (flatHalfRaisingL j).adjoint

lemma scalarModelLoweringDirectionalLinear_apply (d : Data) (y v : X) :
    scalarModelLoweringDirectionalLinear d y v=(framedRaisingHalfL d y v).adjoint := by
  simp only [scalarModelLoweringDirectionalLinear,framedRaisingHalfL,_root_.sum_apply,
    ContinuousLinearMap.smulRight_apply,map_sum,map_smul]

/-- The actual complete forward model has a fixed-coordinate weak form;
its degree part uses the SAME ambient section as its derivative part. -/
theorem scalarModelForwardWeakSection_coordinate (d : Data) (U : X → SphereSobolev (5/2:ℝ)) (y : X)
    (hFrame : ∀ i j,metricPair d.γ y (d.frame y i) (d.frame y j)=if i=j then 1 else 0) :
    scalarModelForwardWeakSection d U y=
      ∑ k : I,∑ c : I,(d.γ y)⁻¹ k c • (
        framedRaisingHalfL d y (axis c)
          (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num) (fiveHalfCovariantDerivative d U (axis k) y))+
        coordDeriv k (fun x => Real.log (d.radius x)) y • framedRaisingHalfL d y (axis c)
          (degreeHigherL (sphereSobolevInclusionL (5/2:ℝ) (3/2:ℝ) (by norm_num) (U y)))) := by
  let J := sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)
  let u := sphereSobolevInclusionL (5/2:ℝ) (3/2:ℝ) (by norm_num) (U y)
  let V : X →L[ℝ] SphereSobolev (1/2:ℝ) :=
    J.comp (scalarModelFirstDerivativeLinear d U y)+(fderiv ℝ (fun x => Real.log (d.radius x)) y).smulRight (degreeHigherL u)
  have hV (v : X) : V v=J (fiveHalfCovariantDerivative d U v y)+
      fderiv ℝ (fun x => Real.log (d.radius x)) y v • degreeHigherL u := by
    simp only [V,_root_.add_apply,ContinuousLinearMap.comp_apply,ContinuousLinearMap.smulRight_apply,
      scalarModelFirstDerivativeLinear_apply]
  have hTrace := scalar_model_linear_frame_trace d.γ d.frame y hFrame (scalarModelRaisingDirectionalLinear d y) V
  have hLeft : scalarModelForwardWeakSection d U y=
      ∑ i : I,scalarModelRaisingDirectionalLinear d y (d.frame y i) (V (d.frame y i)) := by
    apply Finset.sum_congr rfl
    intro i _
    rw [scalarModelRaisingDirectionalLinear_apply,framedRaisingHalfL_frame d y hFrame,hV]
    rfl
  rw [hLeft,hTrace]
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro c _
  rw [scalarModelRaisingDirectionalLinear_apply,hV,map_add,map_smul]
  rfl

lemma scalar_model_linear_map_neg_add_smul {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    (L : E →L[ℝ] F) (v z : E) (t : ℝ) :
    L (-v+t • z)= -L v+t • L z := by
  rw [map_add,map_neg,map_smul]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The corrected lowering model is the SAME genuine adjoint-leading
coefficient with its degree-minus-one zeroth term retained. -/
theorem scalarModelAdjointWeakSection_coordinate (d : Data) (U : X → SphereSobolev (5/2:ℝ)) (y : X)
    (hFrame : ∀ i j,metricPair d.γ y (d.frame y i) (d.frame y j)=if i=j then 1 else 0) :
    scalarModelAdjointWeakSection d U y=
      ∑ k : I,∑ c : I,(d.γ y)⁻¹ k c • (
        -(framedRaisingHalfL d y (axis c)).adjoint
          (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num) (fiveHalfCovariantDerivative d U (axis k) y))+
        coordDeriv k (fun x => Real.log (d.radius x)) y • (framedRaisingHalfL d y (axis c)).adjoint
          (degreeHigherL (sphereSobolevInclusionL (5/2:ℝ) (3/2:ℝ) (by norm_num) (U y))-
            sphereSobolevInclusionL (5/2:ℝ) (1/2:ℝ) (by norm_num) (U y))) := by
  let J := sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)
  let u := sphereSobolevInclusionL (5/2:ℝ) (3/2:ℝ) (by norm_num) (U y)
  let V : X →L[ℝ] SphereSobolev (1/2:ℝ) :=
    -(J.comp (scalarModelFirstDerivativeLinear d U y))+
      (fderiv ℝ (fun x => Real.log (d.radius x)) y).smulRight (degreeHigherL u-J u)
  have hV (v : X) : V v= -J (fiveHalfCovariantDerivative d U v y)+
      fderiv ℝ (fun x => Real.log (d.radius x)) y v • (degreeHigherL u-J u) := by
    simp only [V,_root_.add_apply,_root_.neg_apply,ContinuousLinearMap.comp_apply,ContinuousLinearMap.smulRight_apply,
      scalarModelFirstDerivativeLinear_apply]
  have hTrace := scalar_model_linear_frame_trace d.γ d.frame y hFrame (scalarModelLoweringDirectionalLinear d y) V
  have hLeft : scalarModelAdjointWeakSection d U y=
      ∑ i : I,scalarModelLoweringDirectionalLinear d y (d.frame y i) (V (d.frame y i)) := by
    apply Finset.sum_congr rfl
    intro i _
    rw [scalarModelLoweringDirectionalLinear_apply,framedRaisingHalfL_frame d y hFrame,hV]
    rfl
  calc
    _ = ∑ i : I,scalarModelLoweringDirectionalLinear d y (d.frame y i) (V (d.frame y i)) := hLeft
    _ = ∑ k : I,∑ c : I,(d.γ y)⁻¹ k c • scalarModelLoweringDirectionalLinear d y (axis c) (V (axis k)) := hTrace
    _ = _ := by
      apply Finset.sum_congr rfl
      intro k _
      apply Finset.sum_congr rfl
      intro c _
      apply congrArg (fun z : SphereSobolev (-(1/2:ℝ)) => (d.γ y)⁻¹ k c • z)
      calc
        _ = (framedRaisingHalfL d y (axis c)).adjoint (V (axis k)) :=
          congrArg (fun L : SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ)) => L (V (axis k)))
            (scalarModelLoweringDirectionalLinear_apply d y (axis c))
        _ = (framedRaisingHalfL d y (axis c)).adjoint
            (-J (fiveHalfCovariantDerivative d U (axis k) y)+
              fderiv ℝ (fun x => Real.log (d.radius x)) y (axis k) • (degreeHigherL u-J u)) :=
          congrArg ((framedRaisingHalfL d y (axis c)).adjoint) (hV (axis k))
        _ = _ := by
          have hLinear := scalar_model_linear_map_neg_add_smul
            ((framedRaisingHalfL d y (axis c)).adjoint)
            (J (fiveHalfCovariantDerivative d U (axis k) y)) (degreeHigherL u-J u)
            (fderiv ℝ (fun x => Real.log (d.radius x)) y (axis k))
          simpa only [u,J,sphereSobolevInclusionL_trans_apply,coordDeriv] using hLinear

end ShrinkingSpheres.ParallelEnergy
