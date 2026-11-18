import Proof.NormalGeodesicEnergyVariation
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1400000
set_option maxSynthPendingDepth 30
open Set Filter
open scoped ContDiff Topology
namespace ShrinkingSpheres

lemma NormalCoordinates.gauss_phase {Y Ω : Set X} (hΩ : IsOpen Ω)
    {K : ℝ} {g : MetricField} (hg : Elliptic Ω K g) (hK : 0 < K)
    {expMap : X × X → X} {R : X → ℝ}
    (hN : NormalCoordinates Y Ω g expMap R) {y : X} (hy : y ∈ Y) (hyΩ : y ∈ Ω)
    (v u : X) (hv : v ∈ interior (disk g y (R y))) {t : ℝ} (ht : t ∈ Icc (0:ℝ) 1) :
    metricPair g (normalGeodesicPhase expMap y (v,t)).1
      (normalGeodesicPhase expMap y (v,t)).2 (normalVelocityVariation expMap y v u t).1 =
      t*metricPair g y v u := by
  let P := fun s : ℝ => normalGeodesicPhase expMap y (v,s)
  let J := normalVelocityVariation expMap y v u
  let c := metricPair g y v u
  let F := fun s : ℝ => metricPair g (P s).1 (P s).2 (J s).1-s*c
  have hDerivative (s : ℝ) (hs : s ∈ Icc (0:ℝ) 1) : HasDerivAt F 0 s := by
    have hPhase := hN.hasDerivAt_phase hy v (interior_subset hv) hs
    have hPos := hasDerivAt_prod_fst hPhase
    have hVel := hasDerivAt_prod_snd hPhase
    have hJ := hN.hasDerivAt_variation_position hΩ hg hK hy v u hv hs
    have hx : (P s).1 ∈ Ω := hN.path_image hy v (interior_subset hv) hs
    have hPair := hasDerivAt_metricPair_curve hΩ hg hPos hVel hJ hx
    have hEnergy := hN.geodesic_energy_variation hΩ hg hK hy hyΩ v u hv hs
    have hM1 := connection_metric hΩ hg hK hx (P s).2 (P s).2 (J s).1
    have hM2 := connection_metric hΩ hg hK hx (J s).1 (P s).2 (P s).2
    have hSymm1 := metricPair_symm g (P s).1 (J s).2 (P s).2 (hg.2 _ hx).1
    have hSymm2 := metricPair_symm g (P s).1
      (connection g (P s).1 (J s).1 (P s).2) (P s).2 (hg.2 _ hx).1
    have hΓ := connection_symmetric hΩ hg hx (J s).1 (P s).2
    rw [hΓ] at hM2 hSymm2
    have hVal : metricDifferential g (P s).1 (P s).2 (P s).2 (J s).1+
        metricPair g (P s).1 (-connection g (P s).1 (P s).2 (P s).2) (J s).1+
        metricPair g (P s).1 (P s).2 (J s).2 = c := by
      simp only [← metricBilinear_apply,map_neg,_root_.neg_apply]
      simp only [metricBilinear_apply]
      change metricDifferential g (P s).1 (J s).1 (P s).2 (P s).2+
        metricPair g (P s).1 (J s).2 (P s).2+
        metricPair g (P s).1 (P s).2 (J s).2=2*c at hEnergy
      linarith only [hEnergy,hM1,hM2,hSymm1,hSymm2]
    change HasDerivAt (fun q => metricPair g (P q).1 (P q).2 (J q).1)
      (metricDifferential g (P s).1 (P s).2 (P s).2 (J s).1+
        metricPair g (P s).1 (-connection g (P s).1 (P s).2 (P s).2) (J s).1+
        metricPair g (P s).1 (P s).2 (J s).2) s at hPair
    have hh := hPair.sub ((hasDerivAt_id s).mul_const c)
    exact hh.congr_deriv (by simpa only [one_mul] using sub_eq_zero.mpr hVal)
  have hzero : (0:ℝ) ∈ Icc (0:ℝ) 1 := by constructor <;> norm_num
  have hBound := (convex_Icc (0:ℝ) 1).norm_image_sub_le_of_norm_hasDerivWithin_le (C:=0)
    (fun s hs => (hDerivative s hs).hasDerivWithinAt) (fun _ _ => by norm_num) hzero ht
  have hEq : F t=F 0 := sub_eq_zero.mp (norm_eq_zero.mp
    (le_antisymm (by simpa only [zero_mul] using hBound) (norm_nonneg _)))
  have hF0 : F 0=0 := by
    simp only [F,P,J,normalVelocityVariation,hN.phase_zero hy v (interior_subset hv),
      hN.phase_variation_zero hy v u hv,zero_mul,sub_zero,← metricBilinear_apply,map_zero]
  exact sub_eq_zero.mp (hEq.trans hF0)
end ShrinkingSpheres
