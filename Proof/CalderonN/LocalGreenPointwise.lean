module

public import Proof.CalderonN.AffineChart
public import Proof.CalderonN.GreenWeak
import Proof.CalderonN.CompactSmoothExtension
import Proof.CalderonN.InteriorPointwise
import Proof.CalderonN.EuclideanVolume
import Mathlib.Tactic

public section

/- LocalGreenPointwise in the 3D Theorem 3.1 release, keeping the explicit
   squared-L² premise so the separated Green estimate has a checked caller. -/
noncomputable section
open Set Metric Filter MeasureTheory
open scoped ContDiff Topology Pointwise

namespace CalderonN
open Elliptic
variable {n : ℕ} [NeZero n]

set_option maxHeartbeats 2200000 in
/-- The actual Green germ satisfies its inverse-distance estimate in a
fixed chart neighborhood. The constant is independent of both points. -/
theorem exists_Green_distance_bound_of_offPoleL2
    {Ω : Set (X n)} (hΩ : IsOpen Ω) {g : (MetricField n)} (hg : SmoothMetric univ g)
    {G : (X n) × (X n) → ℝ} (hG : GreenGerm Ω g G)
    (hCover : closedBall (0 : X n) 1 ⊆ Ω)
    {N : ℝ} (hN : 0 ≤ N)
    (hTest : ∀ y ∈ closedBall (0 : X n) (1/4), ∀ x : X n, ∀ r ∈ Ioc (0:ℝ) (1/4),
      closedBall x r ⊆ closedBall (0 : X n) (1/2) → 2 * r ≤ dist x y →
      (∫ z in ball x (r/2), G (z,y)^2) ≤ N * r ^ (4 - (n : ℝ))) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ closedBall (0:(X n)) (1/8), ∀ y ∈ closedBall (0:(X n)) (1/8),
      x ≠ y → |G (x,y)| ≤ C * dist x y ^ (2 - (n : ℝ)) := by
  let Q := closedBall (0:(X n)) (1/8)
  let U := ball (0:(X n)) (1/2)
  let J : Set ((X n) × ℝ) := Q ×ˢ Icc (0:ℝ) (1/4)
  let a (p : (X n) × ℝ) (i j : (I n)) (z : (X n)) := divergenceCoeff (affineChartMetric g p) z i j
  have ha (i j : (I n)) : Strict.JointSmooth (fun p => a p i j) :=
    contDiff_affineChartMetric_divergenceCoeff hg i j
  have hPos (p : (X n) × ℝ) (_ : p ∈ J) (z : (X n)) (_ : z ∈ U) :
      (show (Mat n) from fun i j => a p i j z).PosDef :=
    divergenceMatrix_posDef (affineChartMetric g p) z
      ((smoothMetric_affineChartMetric hg p).2 z (mem_univ _))
  have h0 : (0:(X n)) ∈ U := mem_ball_self (by norm_num)
  obtain ⟨D,hD,hPoint⟩ := exists_interior_word_point_bound_family
    ((isCompact_closedBall (0:(X n)) (1/8)).prod isCompact_Icc)
    (isOpen_ball : IsOpen U) (isCompact_singleton (x := (0:(X n))))
    (singleton_subset_iff.mpr h0) a ha hPos []
  let K := (1 / 2 : ℝ) ^ (2 - (n : ℝ))
  have hK : 0 ≤ K := Real.rpow_nonneg (by norm_num) _
  refine ⟨D * Real.sqrt N * K, by positivity, ?_⟩
  intro x hx y hy hxy
  let d := dist x y
  let r := d/2
  have hd : 0 < d := dist_pos.mpr hxy
  have hr : 0 < r := half_pos hd
  have hx' := mem_closedBall_zero_iff.mp hx
  have hy' := mem_closedBall_zero_iff.mp hy
  have hds : d ≤ 1/4 := by
    dsimp only [d]
    linarith [dist_triangle x (0:(X n)) y,dist_zero_right x,dist_zero_left y]
  have hr' : r ∈ Ioc (0:ℝ) (1/4) := ⟨hr,by dsimp only [r]; linarith⟩
  have hrd : r < dist x y := half_lt_self hd
  have hSub : closedBall x r ⊆ closedBall (0:(X n)) (1/2) := by
    intro z hz
    have h := mem_closedBall.mp hz
    apply mem_closedBall.mpr
    linarith [dist_triangle z x (0:(X n)),dist_zero_right x,hr'.2]
  have hSep : 2 * r ≤ dist x y := by dsimp [r, d]; linarith
  have hL2 := hTest y (closedBall_subset_closedBall (by norm_num) hy) x r hr' hSub hSep
  let V := Ω \ {y}
  have hV : IsOpen V := hΩ.sdiff isClosed_singleton
  have hyO : y ∈ Ω := hCover ((closedBall_subset_closedBall (by norm_num)) hy)
  have hGf := hG.harmonic_left hΩ
    ⟨fun i j => (hg.1 i j).mono (subset_univ Ω),fun z _ => hg.2 z (mem_univ _)⟩ hyO
  have hSubV : closedBall x r ⊆ V := by
    intro z hz
    refine ⟨hCover ((closedBall_subset_closedBall (by norm_num)) (hSub hz)),?_⟩
    intro h
    have he : z = y := h
    have hh := mem_closedBall.mp hz
    rw [he,dist_comm] at hh
    exact hrd.not_ge hh
  obtain ⟨b,hb,_,W,hW,hCW,hWV,hbG⟩ := exists_contDiff_extension_near_compact hV
    (isCompact_closedBall x r) hSubV hGf.1
  let F := affineChartMap x r
  let u := b ∘ F
  let γ := affineChartMetric g (x,r)
  have hγ : SmoothMetric univ γ := smoothMetric_affineChartMetric hg (x,r)
  have hu : ContDiff ℝ ∞ u := hb.comp (contDiff_affineChartMap x r)
  have hMap (z : (X n)) (hz : z ∈ U) : F z ∈ closedBall x r := by
    have h := mem_ball_zero_iff.mp hz
    rw [mem_closedBall,dist_eq_norm]
    change ‖(x+r • z)-x‖ ≤ r
    rw [add_sub_cancel_left,norm_smul,Real.norm_eq_abs,abs_of_pos hr]
    exact mul_le_of_le_one_right hr.le (h.le.trans (by norm_num))
  have hEq (z : (X n)) (hz : z ∈ U) : u z = G (F z,y) := hbG (hCW (hMap z hz))
  have hLap (z : (X n)) (hz : z ∈ U) : Lop (a (x,r)) u z = 0 := by
    have hbLap : laplace g b (F z) = 0 :=
      (laplace_congrOn hW (fun _ _ => rfl) hbG (hCW (hMap z hz))).trans (hGf.2 _ (hSubV (hMap z hz)))
    have he := laplace_affineChart isOpen_univ hg hb.contDiffOn x r (x := z) (mem_univ _)
    change laplace γ u z = r^2 * laplace g b (F z) at he
    rw [hbLap,mul_zero] at he
    change (∑ i, coordDeriv i (fun v => divergenceFlux γ u v i) z) = 0
    rw [← chartVolume_mul_laplace_eq_divergence isOpen_univ hγ hu.contDiffOn (mem_univ z),he,mul_zero]
  have huInt : IntegrableOn (fun z => u z^2) U :=
    ((hu.continuous.pow 2).continuousOn.integrableOn_compact (isCompact_closedBall (0:(X n)) (1/2))).mono_set
      ball_subset_closedBall
  have h := hPoint (x,r) ⟨hx,hr.le,hr'.2⟩ u hu hLap huInt 0 (mem_singleton _)
  change |u 0| ≤ D * Real.sqrt (∫ z in U, u z ^ 2) at h
  have hE : u 0 = G (x,y) := by
    simpa only [F, affineChartMap, smul_zero, add_zero] using hEq 0 h0
  rw [hE] at h
  rw [setIntegral_congr_fun isOpen_ball.measurableSet
    (fun z hz => congrArg (fun t : ℝ => t^2) (hEq z hz))] at h
  have hpow := abs_le_rpow_of_rescaled_L2_bound (f := fun z => G (z,y)) x hr hN hD hL2 h
  refine hpow.trans_eq ?_
  have hr' : r = (1 / 2 : ℝ) * d := by dsimp [r]; ring
  rw [hr', Real.mul_rpow (by norm_num : 0 ≤ (1 / 2 : ℝ)) hd.le, ← mul_assoc]

end CalderonN
