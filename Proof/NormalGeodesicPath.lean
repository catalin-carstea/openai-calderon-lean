import Proof.NormalPullbackMetric
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.MeanValue

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open Set
open scoped ContDiff
namespace ShrinkingSpheres

lemma smul_mem_disk_of_mem (g : MetricField) (y v : X) (R t : ℝ)
    (hv : v ∈ disk g y R) (ht : t ∈ Icc (0:ℝ) 1) : t • v ∈ disk g y R := by
  change metricPair g y v v ≤ R^2 at hv
  change metricPair g y (t • v) (t • v) ≤ R^2
  rw [metricPair_smul_left,metricPair_smul_right]
  have ht2 : t^2 ≤ 1 := by nlinarith [ht.1,ht.2]
  by_cases hq : 0 ≤ metricPair g y v v
  · have hh := mul_le_mul_of_nonneg_right ht2 hq
    nlinarith only [hh,hv]
  · have hh := mul_nonpos_of_nonneg_of_nonpos (sq_nonneg t) (le_of_not_ge hq)
    nlinarith only [hh,sq_nonneg R]

/-- The complete admitted radial geodesic has a smooth neighborhood of its closed
    parameter interval, obtained from the same normal-coordinate tube. -/
theorem NormalCoordinates.smoothNear_path {Y Ω : Set X} {g : MetricField}
    {expMap : X × X → X} {R : X → ℝ}
    (hN : NormalCoordinates Y Ω g expMap R) {y : X} (hy : y ∈ Y)
    (v : X) (hv : v ∈ disk g y (R y)) :
    smoothNear (fun t : ℝ => expMap (y,t • v)) (Icc (0:ℝ) 1) := by
  obtain ⟨U,hU,hTube,hReg⟩ := hN.1
  have hc : ContDiff ℝ ∞ (fun t : ℝ => (y,t • v)) :=
    contDiff_const.prodMk (contDiff_id.smul contDiff_const)
  refine ⟨(fun t : ℝ => (y,t • v)) ⁻¹' U,hU.preimage hc.continuous,?_,?_⟩
  · intro t ht
    exact hTube ⟨hy,smul_mem_disk_of_mem g y v (R y) t hv ht⟩
  · exact hReg.comp hc.contDiffOn (fun _ ht => ht)

lemma NormalCoordinates.path_image {Y Ω : Set X} {g : MetricField}
    {expMap : X × X → X} {R : X → ℝ}
    (hN : NormalCoordinates Y Ω g expMap R) {y : X} (hy : y ∈ Y)
    (v : X) (hv : v ∈ disk g y (R y)) {t : ℝ} (ht : t ∈ Icc (0:ℝ) 1) :
    expMap (y,t • v) ∈ Ω :=
  ((hN.2 y hy).2.2 (t • v) (smul_mem_disk_of_mem g y v (R y) t hv ht)).1

/-- Conservation of the actual metric speed along every admitted radial geodesic. -/
theorem NormalCoordinates.geodesic_energy_constant {Y Ω : Set X} (hΩ : IsOpen Ω)
    {K : ℝ} {g : MetricField} (hg : Elliptic Ω K g) (hK : 0 < K)
    {expMap : X × X → X} {R : X → ℝ}
    (hN : NormalCoordinates Y Ω g expMap R) {y : X} (hy : y ∈ Y)
    (v : X) (hv : v ∈ disk g y (R y)) {t : ℝ} (ht : t ∈ Icc (0:ℝ) 1) :
    metricPair g (expMap (y,t • v))
      (deriv (fun s : ℝ => expMap (y,s • v)) t)
      (deriv (fun s : ℝ => expMap (y,s • v)) t) = metricPair g y v v := by
  let path : ℝ → X := fun s => expMap (y,s • v)
  let E : ℝ → ℝ := fun s => metricPair g (path s) (deriv path s) (deriv path s)
  obtain ⟨U,hU,hI,hReg⟩ := hN.smoothNear_path hy v hv
  have hVel : ContDiffOn ℝ ∞ (deriv path) U := hReg.deriv_of_isOpen hU (by simp)
  have hEnergy (s : ℝ) (hs : s ∈ Icc (0:ℝ) 1) : HasDerivAt E 0 s := by
    have hpath := ((hReg.contDiffAt (hU.mem_nhds (hI hs))).differentiableAt (by simp)).hasDerivAt
    have hvel := ((hVel.contDiffAt (hU.mem_nhds (hI hs))).differentiableAt (by simp)).hasDerivAt
    have hODE : deriv (deriv path) s = -connection g (path s) (deriv path s) (deriv path s) :=
      ((hN.2 y hy).2.2 v hv).2.2.2.2 s hs
    rw [hODE] at hvel
    have hmet := hasDerivAt_metricPair_curve hΩ hg hpath hvel hvel (hN.path_image hy v hv hs)
    have hm := connection_metric hΩ hg hK (hN.path_image hy v hv hs)
      (deriv path s) (deriv path s) (deriv path s)
    have hval : metricDifferential g (path s) (deriv path s) (deriv path s) (deriv path s)+
        metricPair g (path s) (-connection g (path s) (deriv path s) (deriv path s)) (deriv path s)+
        metricPair g (path s) (deriv path s) (-connection g (path s) (deriv path s) (deriv path s)) = 0 := by
      simp only [← metricBilinear_apply,map_neg,_root_.neg_apply]
      simp only [metricBilinear_apply]
      linarith only [hm]
    rw [hval] at hmet
    exact hmet
  have hzero : (0:ℝ) ∈ Icc (0:ℝ) 1 := by constructor <;> norm_num
  have hbound := (convex_Icc (0:ℝ) 1).norm_image_sub_le_of_norm_hasDerivWithin_le (C:=0)
    (fun s hs => (hEnergy s hs).hasDerivWithinAt) (fun _ _ => by norm_num) hzero ht
  have hb0 : ‖E t-E 0‖ ≤ 0 := by simpa only [zero_mul] using hbound
  have heq : E t = E 0 := sub_eq_zero.mp (norm_eq_zero.mp (le_antisymm hb0 (norm_nonneg _)))
  have hGeo := (hN.2 y hy).2.2 v hv
  simpa only [E,path,hGeo.2.2.1,hGeo.2.2.2.1] using heq

end ShrinkingSpheres
