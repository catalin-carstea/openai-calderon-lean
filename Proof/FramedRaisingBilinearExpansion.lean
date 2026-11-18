import Proof.FramedFlatRaisingSobolev
import Proof.FrameTensorMatrix
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2600000
set_option maxSynthPendingDepth 30
set_option maxRecDepth 2400
open Set
open scoped ContDiff Topology
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.SphereHarmonic

lemma framedFlatRaisingSobolevL_bilinear_axis_expansion (s : ℝ) (g : MetricField)
    (e : Frame) (y v w : X) :
    (framedFlatRaisingSobolevL (s-1) g e y v).comp (framedFlatRaisingSobolevL s g e y w)=
      ∑ a : I,∑ b : I,(v a*w b) •
        (framedFlatRaisingSobolevL (s-1) g e y (axis a)).comp (framedFlatRaisingSobolevL s g e y (axis b)) := by
  rw [framedFlatRaisingSobolevL_axis_expansion (s-1) g e y v,framedFlatRaisingSobolevL_axis_expansion s g e y w]
  apply DFunLike.ext
  intro u
  simp only [ContinuousLinearMap.comp_apply,_root_.sum_apply,_root_.smul_apply,
    map_sum,map_smul,Finset.smul_sum,smul_smul]
  rw [Finset.sum_comm]
  simp only [mul_comm]

lemma framedFlatRaisingSobolevL_matrix_contraction (s : ℝ) (g : MetricField) (e : Frame) (y : X)
    (he : ∀ i j,metricPair g y (e y i) (e y j)=if i=j then 1 else 0) (Q : Mat) :
    (∑ a : I,∑ b : I,Q a b • (framedFlatRaisingSobolevL (s-1) g e y (axis a)).comp
      (framedFlatRaisingSobolevL s g e y (axis b)))=
    ∑ i : I,∑ j : I,frameTensorMatrix g e y Q i j • (flatRaisingSobolevL (s-1) i).comp (flatRaisingSobolevL s j) := by
  calc
    _ = ∑ i : I,∑ j : I,frameTensorMatrix g e y Q i j •
        (∑ a : I,∑ b : I,(e y i a*e y j b) • (framedFlatRaisingSobolevL (s-1) g e y (axis a)).comp
          (framedFlatRaisingSobolevL s g e y (axis b))) := frameTensorMatrix_contraction g e y he Q _
    _ = ∑ i : I,∑ j : I,frameTensorMatrix g e y Q i j •
        (framedFlatRaisingSobolevL (s-1) g e y (e y i)).comp (framedFlatRaisingSobolevL s g e y (e y j)) := by
      simp only [← framedFlatRaisingSobolevL_bilinear_axis_expansion]
    _ = _ := by simp only [framedFlatRaisingSobolevL_frame _ g e y he]

lemma frameTensorMatrix_div (g : MetricField) (e : Frame) (y : X) (Q : Mat) (r : ℝ) (i j : I) :
    frameTensorMatrix g e y (fun a b => Q a b/r) i j=frameTensorMatrix g e y Q i j/r := by
  simp only [frameTensorMatrix,Fin.sum_univ_three]
  ring
end ShrinkingSpheres
