module

public import Proof.CalderonN.ActualCenterRadialResponse
public import Proof.CalderonN.ActualParametricResponseDerivative

import Proof.CalderonN.NormalCenterBoundaryChainRule
import Proof.CalderonN.NormalizedVelocityAtZero
import Mathlib.Tactic

/-! A genuine smooth coefficient along a locally transported center frame,
with its physical radius held fixed. -/

public section

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4300000
set_option maxSynthPendingDepth 31
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter Metric
open scoped ContDiff Topology Matrix.Norms.Elementwise
namespace CalderonN
open BallDirichlet

variable {dim : ℕ} [NeZero dim] [Nontrivial (Fin dim)]

private theorem centerChart_positive_smooth_of_frame
    {Y Ω : Set (X dim)} (hΩ : IsOpen Ω) {K ρ c₀ floor ε : ℝ} {m : ℕ}
    {M : Fin (m+1) → ℝ} {Cj : Fin 9 → ℝ} {d : Data dim}
    (hd : Admissible Y Ω K ρ c₀ M Cj floor ε d) (hK : 0 < K)
    {y : X dim} (hy : y ∈ Y) (e : Frame dim)
    (he : ∀ i j, metricPair d.γ y (e y i) (e y j) = if i=j then 1 else 0)
    (z : X dim)
    (hz : frameVectorLinear e y z ∈ disk d.γ y (max ρ (d.radius y))) :
    let p : CenterChartInput dim := ((y,frameVectorLinear e y),(centerInverseDensity d y,z))
    ContDiffAt ℝ ∞ (centerChartCoefficient d) p ∧ (centerChartCoefficient d p).PosDef := by
  let U := frameVectorLinear e y
  let v := U z
  let J := normalVerticalJacobian d.expMap y v
  let p : CenterChartInput dim := ((y,U),(centerInverseDensity d y,z))
  let x := d.expMap (y,v)
  obtain ⟨O,hO,hTube,hExp⟩ := hd.2.1.1
  have hE : ContDiffAt ℝ ∞ d.expMap (y,v) :=
    hExp.contDiffAt (hO.mem_nhds (hTube ⟨hy,hz⟩))
  have hx : x ∈ Ω := ((hd.2.1.2 y hy).2.2 v hz).1
  have hg : ContDiffAt ℝ ∞ d.g₁ x := contDiffAt_pi.mpr fun i => contDiffAt_pi.mpr fun j =>
    (hd.1.2.1.1 i j).contDiffAt (hΩ.mem_nhds hx)
  have hJ : Function.Injective J := (hd.2.1.normalVerticalJacobian_isInvertible hy v hz).bijective.1
  have hU : Function.Injective U := by
    rw [show ⇑U = frameVector e y from funext (frameVectorLinear_apply e y)]
    exact (bijective_frameVector d.γ e y he).1
  have hM : (pullbackMetricMatrix (centerChartPullbackData d p)).PosDef :=
    pullbackMetricMatrix_posDef (q:=centerChartPullbackData d p) (hd.1.2.1.posDef hK hx) (hJ.comp hU)
  refine ⟨contDiffAt_centerChartCoefficient d p hE hg hM,?_⟩
  change ((centerInverseDensity d y) • (Real.sqrt (pullbackMetricMatrix (centerChartPullbackData d p)).det •
    (pullbackMetricMatrix (centerChartPullbackData d p))⁻¹)).PosDef
  exact (hM.inv.smul (Real.sqrt_pos.2 hM.det_pos)).smul
    (inv_pos.mpr (firstMetricDensityFactor_pos _ _ _))

@[expose] def fixedRadiusTransportedCoefficient (d : Data dim) (y a : X dim)
    (F : ℝ → I dim → X dim) (p : ℝ × X dim) : Mat dim :=
  transportedCenterCoefficient d y a
    (fun t => frameVectorLinear (fun _ => F t) (y+t • a)) (p.1,d.radius y • p.2)

theorem exists_local_actualCenter_coefficientFamily
    {Y Ω : Set (X dim)} (hY : IsOpen Y) (hΩ : IsOpen Ω) {m : ℕ}
    {K ρ c₀ floor ε : ℝ} {M : Fin (m+1) → ℝ} {Cj : Fin 9 → ℝ} {d : Data dim}
    (hd : Admissible Y Ω K ρ c₀ M Cj floor ε d) (hK : 0 < K)
    {y : X dim} (hy : y ∈ Y) (a : X dim) (hrρ : 2*d.radius y < ρ) :
    ∃ F : ℝ → I dim → X dim, (∀ i, ContDiff ℝ ∞ (fun t => F t i)) ∧ F 0 = d.frame y ∧
      ∃ V : Set ℝ, IsOpen V ∧ (0 : ℝ) ∈ V ∧
        (∀ t ∈ V, y+t • a ∈ Y ∧
          (∀ i, HasDerivAt (fun s => F s i) (-connection d.γ (y+t • a) a (F t i)) t) ∧
          ∀ i j, metricPair d.γ (y+t • a) (F t i) (F t j) = if i=j then 1 else 0) ∧
      let A := fixedRadiusTransportedCoefficient d y a F
      ContDiffOn ℝ ∞ A (V ×ˢ ball (0 : X dim) 2) ∧
      (∀ p ∈ V ×ˢ ball (0 : X dim) 2, (A p).PosDef) ∧
      (∀ z ∈ ball (0 : X dim) 2,
        A (0,z) = firstNormalVelocityCoefficient d y (d.radius y • frameVector d.frame y z) ∧
        HasDerivAt (fun t => A (t,z)) (scaledCenterCoefficientDerivative d y a z) 0) := by
  have hyΩ := hd.2.1.center_mem hy
  have hFrame := hd.1.2.2.2.2.2.2.2 y hyΩ
  obtain ⟨F,hF,hF₀,hFnear⟩ := hd.1.1.exists_local_center_parallelFrame hΩ hK y a hyΩ
    (d.frame y) hFrame
  let q (t : ℝ) := y+t • a
  let U (t : ℝ) := frameVectorLinear (fun _ => F t) (q t)
  let r := d.radius y
  let A := fixedRadiusTransportedCoefficient d y a F
  have hr := (hd.2.2.2.2.1.2 y hy).1
  have hq : ContDiff ℝ ∞ q := contDiff_const.add (contDiff_id.smul contDiff_const)
  have hq₀ : q 0 = y := by simp [q]
  have hU : ContDiff ℝ ∞ U := contDiff_frameVectorLinear_curve F q hF
  have hU₀ : U 0 = frameVectorLinear d.frame y := by simp [U,hF₀,frameVectorLinear_eq_sum]
  have hUD : HasDerivAt U (parallelFrameFirstJet d y a) 0 :=
    hasDerivAt_parallelFrameOperator d y a F hF₀
      (fun i => by simpa only [zero_smul,add_zero] using hFnear.self_of_nhds.2.1 i)
  have hYN : ∀ᶠ t : ℝ in 𝓝 0, q t ∈ Y := hq.continuous.continuousAt.eventually (hY.mem_nhds (hq₀ ▸ hy))
  obtain ⟨V,hVsub,hV,hV₀⟩ := _root_.mem_nhds_iff.mp (hYN.and hFnear)
  have hCond (t : ℝ) (ht : t ∈ V) :
      q t ∈ Y ∧ (∀ i, HasDerivAt (fun s => F s i) (-connection d.γ (q t) a (F t i)) t) ∧
      ∀ i j, metricPair d.γ (q t) (F t i) (F t j) = if i=j then 1 else 0 :=
    ⟨(hVsub ht).1,(hVsub ht).2.2⟩
  have hDisk (t : ℝ) (ht : t ∈ V) (z : X dim) (hz : z ∈ ball (0 : X dim) 2) :
      U t (r • z) ∈ disk d.γ (q t) (max ρ (d.radius (q t))) := by
    change metricPair d.γ (q t) (U t (r • z)) (U t (r • z)) ≤ (max ρ (d.radius (q t)))^2
    rw [map_smul,metricPair_smul_left,metricPair_smul_right,show U t = frameVectorLinear (fun _ => F t) (q t) from rfl,
      frameVectorLinear_apply,metricPair_frameVector_self d.γ (fun _ => F t) (q t) z (hCond t ht).2.2]
    have hzN : ‖z‖ ≤ 2 := (mem_ball_zero_iff.mp hz).le
    have hBound : r*‖z‖ ≤ max ρ (d.radius (q t)) :=
      ((mul_le_mul_of_nonneg_left hzN hr.le).trans_eq (mul_comm _ _)).trans
        (hrρ.le.trans (le_max_left _ _))
    have hS := (sq_le_sq₀ (mul_nonneg hr.le (norm_nonneg _))
      ((mul_nonneg hr.le (norm_nonneg _)).trans hBound)).mpr hBound
    nlinarith only [hS]
  let S (p : ℝ × X dim) : CenterChartInput dim :=
    ((q p.1,U p.1),(centerInverseDensity d (q p.1),r • p.2))
  have hChart (t : ℝ) (ht : t ∈ V) (z : X dim) (hz : z ∈ ball (0 : X dim) 2) :
      ContDiffAt ℝ ∞ (centerChartCoefficient d) (S (t,z)) ∧
        (centerChartCoefficient d (S (t,z))).PosDef :=
    centerChart_positive_smooth_of_frame hΩ hd hK (hCond t ht).1 (fun _ => F t)
      (hCond t ht).2.2 (r • z) (hDisk t ht z hz)
  refine ⟨F,hF,hF₀,V,hV,hV₀,hCond,?_,?_,?_⟩
  · intro p hp
    have hQ : ContDiffAt ℝ ∞ (fun p : ℝ × X dim => q p.1) p :=
      hq.contDiffAt.comp p contDiffAt_fst
    have hb : ContDiffAt ℝ ∞ (centerInverseDensity d) (q p.1) :=
      (hd.1.contDiffOn_centerInverseDensity hK).contDiffAt
        (hΩ.mem_nhds (hd.2.1.center_mem (hCond p.1 hp.1).1))
    have hb' : ContDiffAt ℝ ∞ (centerInverseDensity d ∘ fun p : ℝ × X dim => q p.1) p := hb.comp p hQ
    have hS : ContDiffAt ℝ ∞ S p :=
      (hQ.prodMk (hU.contDiffAt.comp p contDiffAt_fst)).prodMk
        (hb'.prodMk (contDiffAt_snd.const_smul r))
    exact (((hChart p.1 hp.1 p.2 hp.2).1.comp p hS :
      ContDiffAt ℝ ∞ A p)).contDiffWithinAt
  · intro p hp
    exact (hChart p.1 hp.1 p.2 hp.2).2
  · intro z hz
    have hA₀ : A (0,z) = firstNormalVelocityCoefficient d y (r • frameVector d.frame y z) := by
      change centerChartCoefficient d ((q 0,U 0),(centerInverseDensity d (q 0),r • z)) = _
      rw [hq₀,hU₀]
      simp only [centerChartCoefficient,centerChartPullbackData,firstNormalVelocityCoefficient,
        map_smul,frameVectorLinear_apply,centerInverseDensity]
    have hCh : ContDiffAt ℝ ∞ (centerChartCoefficient d)
        ((y,frameVectorLinear d.frame y),(centerInverseDensity d y,r • z)) := by
      have hh := (hChart 0 hV₀ z hz).1
      change ContDiffAt ℝ ∞ (centerChartCoefficient d)
        ((q 0,U 0),(centerInverseDensity d (q 0),r • z)) at hh
      rwa [hq₀,hU₀] at hh
    have hb := (hd.1.contDiffOn_centerInverseDensity hK).contDiffAt (hΩ.mem_nhds hyΩ)
    exact ⟨hA₀,hasDerivAt_transportedCenterCoefficient d y a (r • z) U hU₀ hUD
      (hb.differentiableAt (by simp)) hCh (contDiffAt_actualCenterCoefficientFamilyJet d y a _ hCh)⟩

end CalderonN
