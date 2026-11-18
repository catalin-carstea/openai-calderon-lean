import Proof.FramedRaisingBilinearExpansion
import Proof.FramedFlatRaisingSobolev
import Proof.PrincipalFrameTrace
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
open Set
open scoped ContDiff Topology
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.SphereHarmonic

lemma framedFlatRaisingSobolevL_double_axis_expansion (s : ℝ) (g : MetricField)
    (e : Frame) (y v : X) :
    (framedFlatRaisingSobolevL (s-1) g e y v).comp (framedFlatRaisingSobolevL s g e y v)=
      ∑ a : I,∑ b : I,(v a*v b) •
        (framedFlatRaisingSobolevL (s-1) g e y (axis a)).comp
          (framedFlatRaisingSobolevL s g e y (axis b)) := by
  exact framedFlatRaisingSobolevL_bilinear_axis_expansion s g e y v v

/-- The pure leading double raising contracted by the actual inverse metric
    vanishes in ordinary base coordinates on the full graded Sobolev domain. -/
theorem framedFlatRaisingSobolevL_inverse_metric_contracted_zero (s : ℝ) (g : MetricField)
    (e : Frame) (y : X) (he : ∀ i j,metricPair g y (e y i) (e y j)=if i=j then 1 else 0) :
    (∑ a : I,∑ b : I,(g y)⁻¹ a b •
      (framedFlatRaisingSobolevL (s-1) g e y (axis a)).comp
        (framedFlatRaisingSobolevL s g e y (axis b)))=0 := by
  calc
    _ = ∑ i : I,∑ a : I,∑ b : I,(e y i a*e y i b) •
        (framedFlatRaisingSobolevL (s-1) g e y (axis a)).comp
          (framedFlatRaisingSobolevL s g e y (axis b)) :=
      (frame_matrix_contraction g e y he _).symm
    _ = ∑ i : I,(framedFlatRaisingSobolevL (s-1) g e y (e y i)).comp
        (framedFlatRaisingSobolevL s g e y (e y i)) :=
      Finset.sum_congr rfl (fun i _ => (framedFlatRaisingSobolevL_double_axis_expansion s g e y (e y i)).symm)
    _ = ∑ i : I,(flatRaisingSobolevL (s-1) i).comp (flatRaisingSobolevL s i) := by
      simp only [framedFlatRaisingSobolevL_frame _ g e y he]
    _ = 0 := flatRaisingSobolevL_contracted_double_zero s
end ShrinkingSpheres
