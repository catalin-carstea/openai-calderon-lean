import Proof.NormalVerticalJacobian
import Proof.NormalJacobiError
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxSynthPendingDepth 30
open Set Filter
open scoped ContDiff Topology
namespace ShrinkingSpheres

lemma NormalCoordinates.geodesic_energy_variation {Y Ω : Set X} (hΩ : IsOpen Ω)
    {K : ℝ} {g : MetricField} (hg : Elliptic Ω K g) (hK : 0 < K)
    {expMap : X × X → X} {R : X → ℝ}
    (hN : NormalCoordinates Y Ω g expMap R) {y : X} (hy : y ∈ Y) (hyΩ : y ∈ Ω)
    (v u : X) (hv : v ∈ interior (disk g y (R y))) {t : ℝ} (ht : t ∈ Icc (0:ℝ) 1) :
    metricDifferential g (normalGeodesicPhase expMap y (v,t)).1
        (normalVelocityVariation expMap y v u t).1
        (normalGeodesicPhase expMap y (v,t)).2 (normalGeodesicPhase expMap y (v,t)).2+
      metricPair g (normalGeodesicPhase expMap y (v,t)).1
        (normalVelocityVariation expMap y v u t).2 (normalGeodesicPhase expMap y (v,t)).2+
      metricPair g (normalGeodesicPhase expMap y (v,t)).1
        (normalGeodesicPhase expMap y (v,t)).2 (normalVelocityVariation expMap y v u t).2 =
      2*metricPair g y v u := by
  let w : ℝ → X := fun s => v+s • u
  let P : ℝ → X × X := fun s => normalGeodesicPhase expMap y (w s,t)
  have hw : HasDerivAt w u 0 := by
    simpa only [w,id_eq,one_smul] using (hasDerivAt_id (0:ℝ)).smul_const u |>.const_add v
  have hw0 : w 0=v := by simp only [w,zero_smul,add_zero]
  have hInput := hw.prodMk (hasDerivAt_const (0:ℝ) t)
  have hPhase := hN.contDiffAt_phase hy (v,t) (smul_mem_disk_of_mem g y v (R y) t (interior_subset hv) ht)
  have hInput0 : (w 0,t)=(v,t) := congrArg (fun z : X => (z,t)) hw0
  have hPhase0 : HasFDerivAt (normalGeodesicPhase expMap y)
      (fderiv ℝ (normalGeodesicPhase expMap y) (v,t)) (w 0,t) := by
    rw [hInput0]
    exact (hPhase.differentiableAt (by simp)).hasFDerivAt
  have hP := hPhase0.comp_hasDerivAt (0:ℝ) hInput
  have hPos : (P 0).1 ∈ Ω := by
    change expMap (y,t • w 0) ∈ Ω
    rw [hw0]
    exact hN.path_image hy v (interior_subset hv) ht
  have hLeft := hasDerivAt_metricPair_curve hΩ hg (hasDerivAt_prod_fst hP)
    (hasDerivAt_prod_snd hP) (hasDerivAt_prod_snd hP) hPos
  have hRight := hasDerivAt_metricPair_curve hΩ hg (hasDerivAt_const (0:ℝ) y) hw hw hyΩ
  have hNear : ∀ᶠ s in 𝓝 (0:ℝ),w s ∈ disk g y (R y) := by
    have hV : disk g y (R y) ∈ 𝓝 (w 0) := by
      rw [hw0]
      exact mem_interior_iff_mem_nhds.mp hv
    exact hw.continuousAt.eventually hV
  have hEq : (fun s => metricPair g (P s).1 (P s).2 (P s).2) =ᶠ[𝓝 (0:ℝ)]
      (fun s => metricPair g y (w s) (w s)) := by
    filter_upwards [hNear] with s hs
    dsimp only [P]
    rw [hN.phase_eq hy (w s) hs ht]
    exact hN.geodesic_energy_constant hΩ hg hK hy (w s) hs ht
  have hh := hLeft.unique (hRight.congr_of_eventuallyEq hEq)
  have hSymm := metricPair_symm g y u v (hg.2 y hyΩ).1
  simpa only [P,w,zero_smul,add_zero,Function.comp_apply,normalVelocityVariation,
    map_zero,_root_.zero_apply,zero_add,hSymm,two_mul] using hh
end ShrinkingSpheres
