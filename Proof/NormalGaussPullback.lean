import Proof.NormalGaussLemma
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1400000
set_option maxSynthPendingDepth 30
open Set Filter
open scoped ContDiff Topology
namespace ShrinkingSpheres
lemma NormalCoordinates.phase_velocity_eq_vertical {Y Ω : Set X} {g : MetricField}
    {expMap : X × X → X} {R : X → ℝ}
    (hN : NormalCoordinates Y Ω g expMap R) {y : X} (hy : y ∈ Y)
    (v : X) (hv : v ∈ disk g y (R y)) {t : ℝ} (ht : t ∈ Icc (0:ℝ) 1) :
    (normalGeodesicPhase expMap y (v,t)).2=normalVerticalJacobian expMap y (t • v) v := by
  obtain ⟨U,hU,hTube,hReg⟩ := hN.1
  have hE : HasFDerivAt expMap (fderiv ℝ expMap (y,t • v)) (y,t • v) :=
    ((hReg.contDiffAt (hU.mem_nhds (hTube ⟨hy,smul_mem_disk_of_mem g y v (R y) t hv ht⟩))).differentiableAt (by simp)).hasFDerivAt
  have hIn : HasDerivAt (fun s : ℝ => (y,s • v)) (0,v) t := by
    simpa only [id_eq,one_smul] using (hasDerivAt_const t y).prodMk ((hasDerivAt_id t).smul_const v)
  have hD := hE.comp_hasDerivAt t hIn
  rw [hN.phase_eq hy v hv ht]
  exact hD.deriv

/-- Gauss's lemma for the actual admitted normal-coordinate map. -/
theorem NormalCoordinates.gauss_vertical {Y Ω : Set X} (hΩ : IsOpen Ω)
    {K : ℝ} {g : MetricField} (hg : Elliptic Ω K g) (hK : 0 < K)
    {expMap : X × X → X} {R : X → ℝ}
    (hN : NormalCoordinates Y Ω g expMap R) {y : X} (hy : y ∈ Y) (hyΩ : y ∈ Ω)
    (v u : X) (hv : v ∈ interior (disk g y (R y))) :
    metricPair g (expMap (y,v)) (normalVerticalJacobian expMap y v v)
      (normalVerticalJacobian expMap y v u)=metricPair g y v u := by
  have hOne : (1:ℝ) ∈ Icc (0:ℝ) 1 := by constructor <;> norm_num
  have hG := hN.gauss_phase hΩ hg hK hy hyΩ v u hv hOne
  have hJ := hN.variation_position_eq hy v u 1
    (by simpa only [id_eq,one_smul] using interior_subset hv)
  rw [hN.phase_velocity_eq_vertical hy v (interior_subset hv) hOne,hJ] at hG
  simpa only [normalGeodesicPhase,normalGeodesicPosition,one_smul,one_mul] using hG
end ShrinkingSpheres
