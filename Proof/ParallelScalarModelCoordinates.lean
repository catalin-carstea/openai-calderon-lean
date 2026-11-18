import Proof.ParallelScalarModelDegreeSections
import Proof.ParallelScalarModelAngularAdjunction
import Proof.FramedRaisingHalfEndpoints
import Proof.PrincipalFrameTrace

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2800000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set
open scoped ContDiff Topology
namespace ShrinkingSpheres.ParallelEnergy
open OAI.AnisotropicCalderon.SphereHarmonic

/-- Contract two genuinely linear directional maps in an orthonormal
moving frame before estimating their fixed-coordinate coefficients. -/
lemma scalar_model_linear_frame_trace {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    (g : MetricField) (e : Frame) (y : X)
    (hFrame : ∀ i j,metricPair g y (e y i) (e y j)=if i=j then 1 else 0)
    (C : X →L[ℝ] E →L[ℝ] F) (V : X →L[ℝ] E) :
    (∑ i : I,C (e y i) (V (e y i)))=
      ∑ k : I,∑ c : I,(g y)⁻¹ k c • C (axis c) (V (axis k)) := by
  have hC (v : X) : C v=∑ c : I,v c • C (axis c) := by
    simpa only [map_sum,map_smul] using (congrArg C (axis_expansion v)).symm
  have hV (v : X) : V v=∑ k : I,v k • V (axis k) := by
    simpa only [map_sum,map_smul] using (congrArg V (axis_expansion v)).symm
  calc
    _ = ∑ i : I,∑ k : I,∑ c : I,(e y i k*e y i c) • C (axis c) (V (axis k)) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [hC,hV]
      simp only [_root_.sum_apply,_root_.smul_apply,map_sum,map_smul,Finset.smul_sum,smul_smul]
    _ = _ := frame_matrix_contraction g e y hFrame _

/-- The selected H5/2 section has one genuine linear first-derivative
map with values in H3/2. No selected endpoint is differentiated here. -/
def scalarModelFirstDerivativeLinear (d : Data) (U : X → SphereSobolev (5/2:ℝ)) (y : X) :
    X →L[ℝ] SphereSobolev (3/2:ℝ) :=
  (sphereSobolevInclusionL (5/2:ℝ) (3/2:ℝ) (by norm_num)).comp (fderiv ℝ U y)-
    ∑ i : I,∑ j : I,((1/2:ℝ) •frameConnectionLinear d.γ d.frame y i j).smulRight
      (sphereSobolevRotationL (5/2:ℝ) i j (U y))

lemma scalarModelFirstDerivativeLinear_apply (d : Data) (U : X → SphereSobolev (5/2:ℝ)) (y v : X) :
    scalarModelFirstDerivativeLinear d U y v=fiveHalfCovariantDerivative d U v y := by
  have hI : sphereSobolevInclusionL (5/2:ℝ) (3/2:ℝ) (by norm_num)=
      sphereSobolevInclusionL (5/2:ℝ) ((5/2:ℝ)-1) (by norm_num) := by congr 1 <;> norm_num
  simp only [scalarModelFirstDerivativeLinear,fiveHalfCovariantDerivative,gradedSphereSectionCovariantDerivative,hI,
    _root_.sub_apply,_root_.sum_apply,ContinuousLinearMap.comp_apply,ContinuousLinearMap.smulRight_apply,
    _root_.smul_apply,smul_eq_mul,frameConnectionLinear_apply]

def scalarModelRaisingDirectionalLinear (d : Data) (y : X) :
    X →L[ℝ] (SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ))) :=
  ∑ j : I,(frameCoordinateLinear d.γ d.frame y j).smulRight (flatHalfRaisingL j)

lemma scalarModelRaisingDirectionalLinear_apply (d : Data) (y v : X) :
    scalarModelRaisingDirectionalLinear d y v=framedRaisingHalfL d y v := by
  simp only [scalarModelRaisingDirectionalLinear,framedRaisingHalfL,_root_.sum_apply,
    ContinuousLinearMap.smulRight_apply]

end ShrinkingSpheres.ParallelEnergy
