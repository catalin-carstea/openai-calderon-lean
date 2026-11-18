import Proof.ParallelNormalizedDensity

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxSynthPendingDepth 30
open Set
open scoped ContDiff
namespace ShrinkingSpheres

/-- The actual normalized density is smooth on a genuine open domain around
    each admitted center/velocity pair, retaining its actual center factor. -/
theorem Background.exists_open_normalized_density_domain {Y Ω : Set X} (hΩ : IsOpen Ω)
    {K : ℝ} {m : ℕ} {M : Fin (m+1) → ℝ} {g g₁ g₂ : MetricField} {e : Frame}
    (h : Background Ω K M g g₁ g₂ e) (hK : 0 < K)
    {E : X × X → X} {R : X → ℝ} (hN : NormalCoordinates Y Ω g E R)
    {y : X} (hy : y ∈ Y) (v : X) (hv : v ∈ disk g y (R y)) :
    ∃ W : Set (X × X),IsOpen W ∧ (y,v) ∈ W ∧
      ContDiffOn ℝ ∞ (normalizedJointFirstDensityFactor g g₁ E) W := by
  obtain ⟨U,hU,hTube,hReg⟩ := hN.1
  let W := (U ∩ E ⁻¹' Ω) ∩ Prod.fst ⁻¹' Ω
  have hW : IsOpen W := (hReg.continuousOn.isOpen_inter_preimage hU hΩ).inter (hΩ.preimage continuous_fst)
  have hImage : E (y,v) ∈ Ω := by
    simpa only [one_smul] using hN.path_image hy v hv (show (1:ℝ) ∈ Icc (0:ℝ) 1 from ⟨zero_le_one,le_rfl⟩)
  refine ⟨W,hW,⟨⟨hTube ⟨hy,hv⟩,hImage⟩,hN.center_mem hy⟩,?_⟩
  have hc := h.firstMetricDensityFactor_smooth hK
  intro q hq
  have hA := (hc.contDiffAt (hΩ.mem_nhds hq.1.2)).comp q (hReg.contDiffAt (hU.mem_nhds hq.1.1))
  have hB := (hc.contDiffAt (hΩ.mem_nhds hq.2)).comp q contDiffAt_fst
  exact (hA.div hB (firstMetricDensityFactor_pos g g₁ q.1).ne').contDiffWithinAt

end ShrinkingSpheres
