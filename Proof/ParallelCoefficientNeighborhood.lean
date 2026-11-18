import Proof.ParallelFirstMetricCoefficient
import Proof.ParallelFrameMetricRegularity

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter
open scoped ContDiff Topology Matrix.Norms.Elementwise
namespace ShrinkingSpheres

/-- The actual normalized first coefficient has a genuine open smooth matrix
    domain around every admitted point of the parallel center family. -/
theorem Background.exists_parallel_normalized_coefficient_domain {Y Ω : Set X} (hΩ : IsOpen Ω)
    {K : ℝ} {m : ℕ} {M : Fin (m+1) → ℝ} {g g₁ g₂ : MetricField} {e : Frame}
    (h : Background Ω K M g g₁ g₂ e) (hK : 0 < K)
    {E : X × X → X} {R : X → ℝ} (hN : NormalCoordinates Y Ω g E R)
    {y : X} (hy : y ∈ Y) (a : X) (r : ℝ) (L : X →L[ℝ] X) (z : X)
    (hv : r • L z ∈ disk g y (R y))
    (hPos : 0 < (parallelFrameNormalMetric g E y a r L (0,z)).det) :
    ∃ S : Set (ℝ × X),IsOpen S ∧ (0,z) ∈ S ∧
      ContDiffOn ℝ ∞ (parallelNormalizedFirstCoefficient g g₁ E y a r L) S ∧
      ∀ p ∈ S,(parallelFrameInput g y a r L p).1 ∈ Ω := by
  let I0 := parallelFrameInput g y a r L
  let G := parallelFrameNormalMetric g E y a r L
  obtain ⟨U,hU,hTube,hReg⟩ := hN.1
  let T := U ∩ E ⁻¹' Ω
  have hT : IsOpen T := hReg.continuousOn.isOpen_inter_preimage hU hΩ
  have hInput := contDiff_parallelFrameInput g y a r L
  let D := I0 ⁻¹' T ∩ (fun p => (I0 p).1) ⁻¹' Ω
  have hD : IsOpen D := (hT.preimage hInput.continuous).inter
    (hΩ.preimage (continuous_fst.comp hInput.continuous))
  have hx : E (y,r • L z) ∈ Ω := by
    simpa only [one_smul] using hN.path_image hy (r • L z) hv (show (1:ℝ) ∈ Icc (0:ℝ) 1 from ⟨zero_le_one,le_rfl⟩)
  have hpD : (0,z) ∈ D := by
    change (I0 (0,z) ∈ T) ∧ (I0 (0,z)).1 ∈ Ω
    simp only [I0,parallelFrameInput,affineParallelFrame_zero,zero_smul,add_zero]
    exact ⟨⟨hTube ⟨hy,hv⟩,hx⟩,hN.center_mem hy⟩
  obtain ⟨S0,hS0,hpS0,hGS0,hDet⟩ := hN.exists_parallel_frame_metric_domain hΩ h.1 hy a r L z hv hPos
  let S := S0 ∩ D
  have hS : IsOpen S := hS0.inter hD
  have hc := h.firstMetricDensityFactor_smooth hK
  have hN0 : ContDiffOn ℝ ∞ (parallelNormalizedDensity g g₁ E y a r L) D := by
    intro p hp
    have hE : ContDiffAt ℝ ∞ E (I0 p) := hReg.contDiffAt (hU.mem_nhds hp.1.1)
    have hEI := hE.comp p hInput.contDiffAt
    have hNum := (hc.contDiffAt (hΩ.mem_nhds hp.1.2)).comp p hEI
    have hDen := (hc.contDiffAt (hΩ.mem_nhds hp.2)).comp p hInput.contDiffAt.fst
    exact (hNum.div hDen (firstMetricDensityFactor_pos _ _ _).ne').contDiffWithinAt
  have hGS (i j : I) : ContDiffOn ℝ ∞ (fun p => G p i j) S := (hGS0 i j).mono inter_subset_left
  have hNe (p) (hp : p ∈ S) : (G p).det ≠ 0 := (hDet p hp.1).ne'
  have hNS : ContDiffOn ℝ ∞ (parallelNormalizedDensity g g₁ E y a r L) S := hN0.mono inter_subset_right
  refine ⟨S,hS,⟨hpS0,hpD⟩,?_,fun p hp => hp.2.2⟩
  apply contDiffOn_pi.mpr
  intro i
  apply contDiffOn_pi.mpr
  intro j p hp
  have hH := (contDiffOn_matrixFamily_density G hGS hNe).mul
    (contDiffOn_matrixFamily_inverse_entry G hGS hNe i j)
  have hProduct := (hNS.mul hH).contDiffAt (hS.mem_nhds hp)
  have hNear : (fun q => parallelNormalizedFirstCoefficient g g₁ E y a r L q i j) =ᶠ[𝓝 p]
      (fun q => parallelNormalizedDensity g g₁ E y a r L q*matrixFamilyCoefficient G q i j) := by
    filter_upwards [hS.mem_nhds hp] with q hq
    exact h.parallelNormalizedFirstCoefficient_eq hK E y a r L q hq.2.1.2 (isUnit_iff_ne_zero.mpr (hNe q hq)) i j
  exact (hProduct.congr_of_eventuallyEq hNear).contDiffWithinAt

end ShrinkingSpheres
