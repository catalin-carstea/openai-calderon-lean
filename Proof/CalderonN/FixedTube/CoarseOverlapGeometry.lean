module

public import Proof.CalderonN.FixedTube.CoarsePatchGeometry

import Mathlib.Tactic

@[expose] public section

noncomputable section
open Set Metric

namespace CalderonN.FixedTube

variable {dim : ℕ} [NeZero dim] [Nontrivial (Fin dim)] {normal : I dim}

/-- A patch has one of the two orientations of the same separated
reference product. -/
@[expose] def orientPair (b : Bool) (q : (X dim) × (X dim)) : (X dim) × (X dim) :=
  if b then q.swap else q

theorem continuous_orientPair (b : Bool) : Continuous (orientPair (dim := dim) b) := by
  cases b
  · exact continuous_id
  · exact continuous_snd.prodMk continuous_fst

theorem orientPair_orientPair (b : Bool) (q : (X dim) × (X dim)) : orientPair b (orientPair b q) = q := by
  cases b <;> rfl

theorem dist_orientPair (b : Bool) (q : (X dim) × (X dim)) :
    dist (orientPair b q).1 (orientPair b q).2 = dist q.1 q.2 := by
  cases b
  · rfl
  · exact dist_comm _ _

@[expose] def lowerPairAt (normal : I dim) (q : (X dim) × (X dim)) (t : ℝ) : (X dim) × (X dim) :=
  (q.1-t • axis normal,q.2-t • axis normal)

theorem continuous_lowerPairAt (q : (X dim) × (X dim)) : Continuous (lowerPairAt normal q) := by
  exact (continuous_const.sub (continuous_id.smul continuous_const)).prodMk
    (continuous_const.sub (continuous_id.smul continuous_const))

theorem orientPair_lowerPairAt (b : Bool) (q : (X dim) × (X dim)) (t : ℝ) :
    orientPair b (lowerPairAt normal q t) = lowerPairAt normal (orientPair b q) t := by
  cases b <;> rfl

@[expose] def lowerSidePairs (normal : I dim) (η : ℝ) : Set ((X dim) × (X dim)) :=
  {q | min (q.1 normal) (q.2 normal) < -η}

theorem isOpen_lowerSidePairs (η : ℝ) : IsOpen (lowerSidePairs normal η) :=
  isOpen_lt
    (((EuclideanSpace.proj (𝕜 := ℝ) normal).continuous.comp continuous_fst).min
      ((EuclideanSpace.proj (𝕜 := ℝ) normal).continuous.comp continuous_snd)) continuous_const

private theorem dist_lowered (x : (X dim)) {t : ℝ} (ht : 0 ≤ t) :
    dist (x-t • axis normal) x = t := by
  rw [dist_eq_norm,show x-t • axis normal-x = -(t • axis normal) by abel]
  simp [norm_smul,axis,Real.norm_eq_abs,abs_of_nonneg ht]

private theorem retained_near_height_le {q : (X dim) × (X dim)} {c : (X dim)} (hc : c normal = 0) {s κ : ℝ}
    (hq : q ∈ retainedPatch c s κ) : q.1 normal ≤ κ*s := by
  have hdist : ‖q.1-c‖ < κ*s := by simpa only [dist_eq_norm] using mem_ball.mp hq.1
  have hcoord := (le_abs_self ((q.1-c) normal)).trans (PiLp.norm_apply_le (q.1-c) normal)
  simp only [PiLp.sub_apply,hc,sub_zero] at hcoord
  exact hcoord.trans hdist.le

private theorem retained_separation_bounds {q : (X dim) × (X dim)} {c : (X dim)} {s κ : ℝ}
    (hs : 0 < s) (hκ : κ ≤ 1/100) (hq : q ∈ retainedPatch c s κ) :
    (89/100)*s < dist q.1 q.2 ∧ dist q.1 q.2 < (111/100)*s := by
  have hnear := mem_ball.mp hq.1
  have haway : 9*s/10 < ‖q.2-c‖ ∧ ‖q.2-c‖ < 11*s/10 := hq.2
  have h₁ := dist_triangle q.2 q.1 c
  rw [dist_comm q.2 q.1,dist_eq_norm q.2 c] at h₁
  have h₂ := dist_triangle q.1 c q.2
  rw [dist_comm c q.2,dist_eq_norm q.2 c] at h₂
  have hm := mul_le_mul_of_nonneg_right hκ hs.le
  constructor <;> linarith [haway.1,haway.2]

private theorem lowerPairAt_mem_coarsePatch {q : (X dim) × (X dim)} {c : (X dim)} {s κ δ t : ℝ}
    (hs : 0 < s) (hκ : κ ≤ 1/100) (hκδ : 5*κ < δ) (ht : 0 ≤ t)
    (hcap : t ≤ 4*κ*s) (hq : q ∈ retainedPatch c s κ) :
    lowerPairAt normal q t ∈ coarsePatch normal c s δ := by
  have hmove₁ := (dist_lowered (normal := normal)) q.1 ht
  have hmove₂ := (dist_lowered (normal := normal)) q.2 ht
  have hNear := dist_triangle (q.1-t • axis normal) q.1 (affineChartMap c s (planeCenter normal))
  rw [hmove₁] at hNear
  have hRoom := dist_triangle q.1 c (affineChartMap c s (planeCenter normal))
  rw [dist_comm c,dist_affineChartMap_center c hs.le,(norm_planeCenter (normal := normal))] at hRoom
  have hqNear := mem_ball.mp hq.1
  have hδs := mul_lt_mul_of_pos_right hκδ hs
  refine ⟨mem_ball.mpr ?_,?_⟩
  · rw [mul_add]
    change dist (q.1-t • axis normal) (affineChartMap c s (planeCenter normal)) <
      s*planeDepth + s*δ
    linarith
  · have hHi := dist_triangle (q.2-t • axis normal) q.2 c
    have hLo := dist_triangle q.2 (q.2-t • axis normal) c
    rw [hmove₂] at hHi
    rw [dist_comm q.2 (q.2-t • axis normal),hmove₂] at hLo
    have hqAway : 9*s/10 < ‖q.2-c‖ ∧ ‖q.2-c‖ < 11*s/10 := hq.2
    rw [← dist_eq_norm] at hqAway
    have hm := mul_le_mul_of_nonneg_right hκ hs.le
    change 4*s/5 < ‖q.2-t • axis normal-c‖ ∧ ‖q.2-t • axis normal-c‖ < 6*s/5
    rw [← dist_eq_norm]
    constructor <;> linarith [hqAway.1,hqAway.2]

set_option maxHeartbeats 450000 in
/-- Any retained overlap admits a common downward interval inside both
larger products. The endpoint belongs to the actual lower-side cross. -/
theorem exists_retained_overlap_lowering {q : (X dim) × (X dim)} {b b' : Bool} {c c' : (X dim)}
    (hc : c normal = 0) (hc' : c' normal = 0) {s s' κ δ δ' η : ℝ}
    (hs : 0 < s) (hs' : 0 < s') (hκ : 0 < κ) (hκcap : κ ≤ 1/100)
    (hκδ : 5*κ < δ) (hκδ' : 5*κ < δ') (hη : 0 < η)
    (hηs : η ≤ κ*s) (hηs' : η ≤ κ*s')
    (hq : orientPair b q ∈ retainedPatch c s κ)
    (hq' : orientPair b' q ∈ retainedPatch c' s' κ) :
    ∃ h > 0, (∀ t ∈ Icc 0 h,
      orientPair b (lowerPairAt normal q t) ∈ coarsePatch normal c s δ ∧
      orientPair b' (lowerPairAt normal q t) ∈ coarsePatch normal c' s' δ') ∧
      lowerPairAt normal q h ∈ lowerSidePairs normal η := by
  have hsep := retained_separation_bounds hs hκcap hq
  have hsep' := retained_separation_bounds hs' hκcap hq'
  rw [dist_orientPair] at hsep hsep'
  have hss' : s ≤ 2*s' := by linarith [hsep.1,hsep'.2]
  have hs's : s' ≤ 2*s := by linarith [hsep'.1,hsep.2]
  let M := max 0 (max ((orientPair b q).1 normal) ((orientPair b' q).1 normal))
  let h := M+2*η
  have hM : 0 ≤ M := le_max_left _ _
  have hh : 0 < h := by dsimp [h]; linarith
  have hx := (retained_near_height_le (normal := normal)) hc hq
  have hx' := (retained_near_height_le (normal := normal)) hc' hq'
  have hBound : h ≤ 4*κ*s := by
    have hMax : M ≤ 2*κ*s := by
      dsimp only [M]
      exact max_le (by positivity) (max_le (hx.trans (by linarith [mul_pos hκ hs]))
        (hx'.trans (by nlinarith only [mul_le_mul_of_nonneg_left hs's hκ.le])))
    dsimp [h]
    linarith
  have hBound' : h ≤ 4*κ*s' := by
    have hMax : M ≤ 2*κ*s' := by
      dsimp only [M]
      exact max_le (by positivity) (max_le
        (hx.trans (by nlinarith only [mul_le_mul_of_nonneg_left hss' hκ.le]))
        (hx'.trans (by linarith [mul_pos hκ hs'])))
    dsimp [h]
    linarith
  refine ⟨h,hh,fun t ht => ?_,?_⟩
  · rw [(orientPair_lowerPairAt (normal := normal)),(orientPair_lowerPairAt (normal := normal))]
    exact ⟨(lowerPairAt_mem_coarsePatch (normal := normal)) hs hκcap hκδ ht.1 (ht.2.trans hBound) hq,
      (lowerPairAt_mem_coarsePatch (normal := normal)) hs' hκcap hκδ' ht.1 (ht.2.trans hBound') hq'⟩
  · have hbase : (orientPair b q).1 normal ≤ M := (le_max_left _ _).trans (le_max_right _ _)
    have hlower : (orientPair b (lowerPairAt normal q h)).1 normal < -η := by
      rw [(orientPair_lowerPairAt (normal := normal))]
      simp only [lowerPairAt,PiLp.sub_apply,PiLp.smul_apply]
      have hAxis : axis normal normal = 1 := by simp [axis]
      rw [hAxis,smul_eq_mul,mul_one]
      dsimp [h]
      linarith
    cases b
    · exact min_lt_iff.mpr (Or.inl hlower)
    · exact min_lt_iff.mpr (Or.inr hlower)

end CalderonN.FixedTube
