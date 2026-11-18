import Proof.ParallelFrameNormalMetric
import Proof.NormalMetricTensorNeighborhood
import Proof.MatrixFamilyCalculus

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set
open scoped ContDiff Topology Matrix.Norms.Operator
namespace ShrinkingSpheres

def parallelFrameInput (g : MetricField) (y a : X) (r : ℝ) (L : X →L[ℝ] X) (p : ℝ × X) : X × X :=
  (y+p.1 • a,r • affineParallelFrame g y a L p.1 p.2)

lemma contDiff_affineParallelFrame (g : MetricField) (y a : X) (L : X →L[ℝ] X) :
    ContDiff ℝ ∞ (affineParallelFrame g y a L) :=
  contDiff_const.sub (contDiff_id.smul contDiff_const)

lemma contDiff_parallelFrameInput (g : MetricField) (y a : X) (r : ℝ) (L : X →L[ℝ] X) :
    ContDiff ℝ ∞ (parallelFrameInput g y a r L) := by
  have hF : ContDiff ℝ ∞ (fun p : ℝ × X => affineParallelFrame g y a L p.1) :=
    (contDiff_affineParallelFrame g y a L).comp contDiff_fst
  exact (contDiff_const.add (contDiff_fst.smul contDiff_const)).prodMk
    ((hF.clm_apply contDiff_snd).const_smul r)

lemma contDiffOn_parallelFrameNormalMetric_entries (g : MetricField) (E : X × X → X)
    (y a : X) (r : ℝ) (L : X →L[ℝ] X) (W : Set (X × X))
    (hT : ContDiffOn ℝ ∞ (normalJointMetricTensor g E) W) (i j : I) :
    ContDiffOn ℝ ∞ (fun p => parallelFrameNormalMetric g E y a r L p i j)
      ((parallelFrameInput g y a r L) ⁻¹' W) := by
  let S := (parallelFrameInput g y a r L) ⁻¹' W
  have hInput := contDiff_parallelFrameInput g y a r L
  have hOp : ContDiffOn ℝ ∞ (normalJointMetricTensor g E ∘ parallelFrameInput g y a r L) S :=
    hT.comp hInput.contDiffOn (fun _ hp => hp)
  have hF : ContDiff ℝ ∞ (fun p : ℝ × X => affineParallelFrame g y a L p.1) :=
    (contDiff_affineParallelFrame g y a L).comp contDiff_fst
  have hSlots := (hOp.clm_apply (hF.clm_apply (contDiff_const (c:=axis i))).contDiffOn).clm_apply
    (hF.clm_apply (contDiff_const (c:=axis j))).contDiffOn
  simpa only [Function.comp_def,normalJointMetricTensor_apply,parallelFrameInput,parallelFrameNormalMetric] using hSlots

/-- A positive determinant at the selected framed point gives a genuine open
    smooth coefficient family around it. No orthonormality away from time0 is asserted. -/
theorem NormalCoordinates.exists_parallel_frame_metric_domain {Y Ω : Set X} (hΩ : IsOpen Ω)
    {K : ℝ} {g : MetricField} (hg : Elliptic Ω K g) {E : X × X → X} {R : X → ℝ}
    (hN : NormalCoordinates Y Ω g E R) {y : X} (hy : y ∈ Y)
    (a : X) (r : ℝ) (L : X →L[ℝ] X) (z : X) (hv : r • L z ∈ disk g y (R y))
    (hPos : 0 < (parallelFrameNormalMetric g E y a r L (0,z)).det) :
    ∃ S : Set (ℝ × X),IsOpen S ∧ ((0:ℝ),z) ∈ S ∧
      (∀ i j,ContDiffOn ℝ ∞ (fun p => parallelFrameNormalMetric g E y a r L p i j) S) ∧
      ∀ p ∈ S,0 < (parallelFrameNormalMetric g E y a r L p).det := by
  obtain ⟨W,hW,hpW,hTW⟩ := hN.exists_open_metric_tensor_domain hΩ hg hy (r • L z) hv
  let U := (parallelFrameInput g y a r L) ⁻¹' W
  have hU : IsOpen U := hW.preimage (contDiff_parallelFrameInput g y a r L).continuous
  have hHere : ((0:ℝ),z) ∈ U := by
    change parallelFrameInput g y a r L (0,z) ∈ W
    simpa only [parallelFrameInput,zero_smul,add_zero,affineParallelFrame_zero] using hpW
  have hG (i j : I) : ContDiffOn ℝ ∞ (fun p => parallelFrameNormalMetric g E y a r L p i j) U :=
    contDiffOn_parallelFrameNormalMetric_entries g E y a r L W hTW i j
  have hDet := contDiffOn_matrixFamily_det (parallelFrameNormalMetric g E y a r L) hG
  let S := U ∩ (fun p => (parallelFrameNormalMetric g E y a r L p).det) ⁻¹' Ioi (0:ℝ)
  have hS : IsOpen S := hDet.continuousOn.isOpen_inter_preimage hU isOpen_Ioi
  refine ⟨S,hS,⟨hHere,hPos⟩,fun i j => (hG i j).mono inter_subset_left,?_⟩
  intro p hp
  exact hp.2

end ShrinkingSpheres
