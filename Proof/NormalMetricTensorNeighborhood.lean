import Proof.NormalMetricTensorFamily

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxSynthPendingDepth 30
open Set
open scoped ContDiff
namespace ShrinkingSpheres

/-- The admitted normal map and metric supply an actual open tensor domain,
    not merely an isolated differentiability assertion. -/
theorem NormalCoordinates.exists_open_metric_tensor_domain {Y Ω : Set X} (hΩ : IsOpen Ω)
    {K : ℝ} {g : MetricField} (hg : Elliptic Ω K g) {E : X × X → X} {R : X → ℝ}
    (hN : NormalCoordinates Y Ω g E R) {y : X} (hy : y ∈ Y) (v : X) (hv : v ∈ disk g y (R y)) :
    ∃ W : Set (X × X),IsOpen W ∧ (y,v) ∈ W ∧ ContDiffOn ℝ ∞ (normalJointMetricTensor g E) W := by
  obtain ⟨U,hU,hTube,hReg⟩ := hN.1
  let W := U ∩ E ⁻¹' Ω
  have hW : IsOpen W := hReg.continuousOn.isOpen_inter_preimage hU hΩ
  have hImage : E (y,v) ∈ Ω := by
    simpa only [one_smul] using hN.path_image hy v hv (show (1:ℝ) ∈ Icc (0:ℝ) 1 from ⟨zero_le_one,le_rfl⟩)
  refine ⟨W,hW,⟨hTube ⟨hy,hv⟩,hImage⟩,?_⟩
  intro q hq
  exact (contDiffAt_normalJointMetricTensor g E q (hReg.contDiffAt (hU.mem_nhds hq.1))
    (fun i j => (hg.1 i j).contDiffAt (hΩ.mem_nhds hq.2))).contDiffWithinAt

end ShrinkingSpheres
