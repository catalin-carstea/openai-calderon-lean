module

public import Proof.CalderonN.ParallelTransportODE
public import Proof.CalderonN.ConnectionOperatorBounds
public import Proof.CalderonN.CompactSmoothExtension

import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic

/-! An orthonormal frame along a short center curve can be transported
using the reference metric on its actual open coordinate region. -/

public section

noncomputable section
open Set Filter Metric
open scoped ContDiff Topology
set_option maxHeartbeats 2400000
set_option maxSynthPendingDepth 24
set_option backward.isDefEq.respectTransparency false

namespace CalderonN

variable {dim : ℕ} [NeZero dim]

theorem Elliptic.exists_local_center_parallelFrame {Ω : Set (X dim)}
    (hΩ : IsOpen Ω) {γ : MetricField dim} {K : ℝ} (hg : Elliptic Ω K γ) (hK : 0 < K)
    (y a : X dim) (hy : y ∈ Ω) (e : I dim → X dim)
    (hE : ∀ i j, metricPair γ y (e i) (e j) = if i=j then 1 else 0) :
    ∃ F : ℝ → I dim → X dim, (∀ i, ContDiff ℝ ∞ (fun t => F t i)) ∧
      F 0 = e ∧ ∀ᶠ t in 𝓝 (0 : ℝ),
        y+t • a ∈ Ω ∧
        (∀ i, HasDerivAt (fun s => F s i) (-connection γ (y+t • a) a (F t i)) t) ∧
        ∀ i j, metricPair γ (y+t • a) (F t i) (F t j) = if i=j then 1 else 0 := by
  let q (t : ℝ) := y+t • a
  have hq : ContDiff ℝ ∞ q := contDiff_const.add (contDiff_id.smul contDiff_const)
  have hq₀ : q 0 = y := by simp [q]
  have hqD (t : ℝ) : HasDerivAt q a t := by
    have ht : HasDerivAt (fun s : ℝ => s • a) a t := by
      simpa only [id_eq,one_smul] using (hasDerivAt_id t).smul_const a
    exact ht.const_add y
  let U := q ⁻¹' Ω
  have hU : IsOpen U := hΩ.preimage hq.continuous
  have h₀ : (0 : ℝ) ∈ U := by change q 0 ∈ Ω; rwa [hq₀]
  let A (t : ℝ) : X dim →L[ℝ] X dim := -connectionBilinear γ (q t) a
  have hA : ContDiffOn ℝ ∞ A U := by
    apply ContDiffOn.neg
    exact (((hg.contDiffOn_connectionBilinear hΩ hK).comp hq.contDiffOn
      (show MapsTo q U Ω from fun _ hx => hx)).clm_apply contDiffOn_const)
  obtain ⟨D,hD,_,W,hW,h0W,_,hDA⟩ := exists_contDiff_extension_near_compact hU
    (isCompact_singleton (x := (0 : ℝ))) (singleton_subset_iff.mpr h₀) hA
  let f (p : ℝ × X dim) := D p.1 p.2
  have hf : ContDiff ℝ ∞ f := (hD.comp contDiff_fst).clm_apply contDiff_snd
  obtain ⟨C,hC⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := 1)).exists_bound_of_continuousOn
    (hD.continuous.norm).continuousOn
  have hGrowth (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) (w : X dim) :
      ‖f (t,w)‖ ≤ max 0 C*‖w‖ :=
    ((D t).le_opNorm w).trans (mul_le_mul_of_nonneg_right
      ((le_abs_self _).trans ((hC t ht).trans (le_max_right _ _))) (norm_nonneg _))
  choose F hF hF₀ hFD using fun i =>
    exists_smooth_solution_of_linearGrowth hf (le_max_left _ _) hGrowth (e i)
  have hzero : (0 : ℝ) ∈ Icc 0 1 := ⟨le_rfl,zero_le_one⟩
  have hDyn : ∀ᶠ t in 𝓝 (0 : ℝ), q t ∈ Ω ∧
      ∀ i, HasDerivAt (fun s => F i s) (-connection γ (q t) a (F i t)) t := by
    filter_upwards [hW.mem_nhds (h0W (mem_singleton _)),hU.mem_nhds h₀,
      Filter.eventually_all.mpr fun i => hFD i 0 hzero] with t htW htU ht
    refine ⟨htU,fun i => ?_⟩
    have ht' := ht i
    change HasDerivAt (F i) (D t (F i t)) t at ht'
    rw [hDA htW] at ht'
    simpa only [A,neg_apply,connectionBilinear_apply] using ht'
  obtain ⟨δ,hδ,hBall⟩ := Metric.mem_nhds_iff.mp hDyn
  have hgS : SmoothMetric Ω γ :=
    ⟨hg.1,fun z hz => hg.posDef hK hz⟩
  refine ⟨fun t i => F i t,fun i => hF i,funext hF₀,?_⟩
  filter_upwards [isOpen_ball.mem_nhds (mem_ball_self hδ)] with t ht
  obtain ⟨hqt,hFt⟩ := hBall ht
  refine ⟨hqt,hFt,fun i j => ?_⟩
  let p (s : ℝ) := metricPair γ (q s) (F i s) (F j s)
  have hDeriv (s : ℝ) (hs : s ∈ uIcc 0 t) : HasDerivAt p 0 s := by
    have hSeg : uIcc (0 : ℝ) t ⊆ ball (0 : ℝ) δ := by
      rw [← segment_eq_uIcc]
      exact (convex_ball (0 : ℝ) δ).segment_subset (mem_ball_self hδ) ht
    obtain ⟨hqs,hFs⟩ := hBall (hSeg hs)
    simpa [p,metricPair] using
      hasDerivAt_metricPair hΩ hgS hqs (hqD s) (hFs i) (hFs j)
  have hI := intervalIntegral.integral_eq_sub_of_hasDerivAt hDeriv
    (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => (0 : ℝ)) MeasureTheory.volume 0 t)
  have hSame : p t = p 0 := sub_eq_zero.mp (by simpa using hI.symm)
  exact hSame.trans (by dsimp only [p]; rw [hq₀,hF₀,hF₀]; exact hE i j)

end CalderonN
