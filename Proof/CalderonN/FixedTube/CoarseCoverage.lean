module

public import Proof.CalderonN.FixedTube.CoarseOverlapGeometry
public import Proof.CalderonN.FixedTube.Initialization

import Mathlib.Tactic

@[expose] public section

noncomputable section
open Set Metric

namespace CalderonN.FixedTube

variable {dim : ℕ} [NeZero dim] [Nontrivial (Fin dim)] {normal : I dim}

structure CoarseAnchor (normal : I dim) (B s₀ s₁ : ℝ) where
  center : (X dim)
  center_bounded : center ∈ closedBall (0 : (X dim)) B
  center_planar : center normal = 0
  scale : ℝ
  scale_range : scale ∈ Icc s₀ s₁

theorem lowerCross_mem_of_norm {q : (X dim) × (X dim)} {B η : ℝ}
    (h₁ : ‖q.1‖ < B) (h₂ : ‖q.2‖ < B) (hsep : q.1 ≠ q.2)
    (hlo : q ∈ lowerSidePairs normal η) : q ∈ lowerCross normal B η := by
  refine ⟨⟨mem_ball_zero_iff.mpr h₁,mem_ball_zero_iff.mpr h₂,hsep⟩,?_⟩
  change min (q.1 normal) (q.2 normal) < -η at hlo
  exact (min_lt_iff.mp hlo).symm

theorem lowerCross_subset_lowerSidePairs (B η : ℝ) : lowerCross normal B η ⊆ lowerSidePairs normal η :=
  fun q h => show min (q.1 normal) (q.2 normal) < -η from min_lt_iff.mpr h.2.symm

set_option maxHeartbeats 450000 in
/-- The retained products cover all near-plane pairs of the coarse
region. A point already below the fixed strip is in the given cross. -/
theorem coarseDomain_cover_lower_or_retained
    {B d κ η M : ℝ} (hd : 0 < d) (hκ : 0 < κ) (hκcap : κ ≤ 1/100)
    (hη : η ≤ κ*d/8) (hM : B ≤ M)
    {q : (X dim) × (X dim)} (hq : q ∈ coarseDomain normal B d (κ/4)) :
    q ∈ lowerCross normal M η ∨
      ∃ b : Bool, ∃ A : CoarseAnchor normal (2*B+1) (d/2) (3*B+1),
        orientPair b q ∈ retainedPatch A.center A.scale κ := by
  have hnorm₁ : ‖q.1‖ < B := hq.1
  have hnorm₂ : ‖q.2‖ < B := hq.2.1
  have hsep : q.1 ≠ q.2 := by
    intro he
    have h := hq.2.2.1
    rw [he,sub_self,norm_zero] at h
    exact hd.not_gt h
  by_cases hlo : q ∈ lowerSidePairs normal η
  · exact Or.inl ((lowerCross_mem_of_norm (normal := normal)) (hnorm₁.trans_le hM) (hnorm₂.trans_le hM) hsep hlo)
  right
  have hcase (x y : (X dim)) (hx : ‖x‖ < B) (hy : ‖y‖ < B) (hsep : d < ‖x-y‖)
      (hheight : -η ≤ x normal ∧ x normal < (κ/4)*‖x-y‖) :
      ∃ A : CoarseAnchor normal (2*B+1) (d/2) (3*B+1), (x,y) ∈ retainedPatch A.center A.scale κ := by
    let c := x - x normal • axis normal
    let r := ‖x-y‖
    let s := ‖y-c‖
    have hAxis : ‖axis normal‖ = 1 := by simp [axis]
    have hc₂ : c normal = 0 := by simp [c,axis,PiLp.sub_apply,PiLp.smul_apply]
    have hX : ‖x-c‖ = |x normal| := by
      dsimp [c]
      rw [sub_sub_cancel,norm_smul,Real.norm_eq_abs,hAxis,mul_one]
    have hxc : ‖x-c‖ ≤ (κ/4)*r := by
      rw [hX,abs_le]
      have hh := mul_lt_mul_of_pos_left hsep (show 0 < κ/4 by positivity)
      constructor <;> linarith [hheight.1,hheight.2,mul_pos hκ hd]
    have hcBound : ‖c‖ ≤ 2*‖x‖ := by
      have h := norm_sub_le x (x normal • axis normal)
      rw [norm_smul,Real.norm_eq_abs,hAxis,mul_one] at h
      have hAbs := PiLp.norm_apply_le x normal
      change |x normal| ≤ ‖x‖ at hAbs
      dsimp [c]
      linarith
    have hr_s : r ≤ s+‖x-c‖ := by
      have h := norm_sub_le (x-c) (y-c)
      rw [sub_sub_sub_cancel_right] at h
      dsimp [r,s]
      linarith
    have hsmall : (κ/4)*r ≤ r/4 := by
      calc
        _ ≤ (1/4 : ℝ)*r :=
          mul_le_mul_of_nonneg_right (by linarith : κ/4 ≤ 1/4) (norm_nonneg (x-y))
        _ = _ := by ring
    have hslo : d/2 < s := by
      change d < r at hsep
      linarith
    have hshi : s ≤ 3*B+1 := by
      dsimp [s]
      have h := norm_sub_le y c
      linarith
    have hC : c ∈ closedBall (0 : (X dim)) (2*B+1) := by
      rw [mem_closedBall,dist_zero_right]
      linarith
    have hspos : 0 < s := by linarith
    have hh : r < 2*s := by
      change d < r at hsep
      linarith
    have hClose : ‖x-c‖ < κ*s := by
      have hLess := mul_lt_mul_of_pos_left hh (show 0 < κ/4 by positivity)
      nlinarith only [hxc,hLess,mul_pos hκ hspos]
    let A : CoarseAnchor normal (2*B+1) (d/2) (3*B+1) := ⟨c,hC,hc₂,s,⟨hslo.le,hshi⟩⟩
    refine ⟨A,mem_ball.mpr ?_,?_⟩
    · simpa only [dist_eq_norm] using hClose
    · change 9*s/10 < s ∧ s < 11*s/10
      constructor <;> linarith
  have hn : -η ≤ min (q.1 normal) (q.2 normal) := le_of_not_gt hlo
  by_cases hmin : q.1 normal ≤ q.2 normal
  · obtain ⟨A,hA⟩ := hcase q.1 q.2 hnorm₁ hnorm₂ hq.2.2.1
      (by simpa only [min_eq_left hmin] using And.intro hn hq.2.2.2)
    exact ⟨false,A,hA⟩
  · have hmin' : q.2 normal ≤ q.1 normal := le_of_not_ge hmin
    have hsep' : d < ‖q.2-q.1‖ := by simpa only [norm_sub_rev q.2 q.1] using hq.2.2.1
    obtain ⟨A,hA⟩ := hcase q.2 q.1 hnorm₂ hnorm₁ hsep' 
      (by simpa only [min_eq_right hmin',norm_sub_rev q.2 q.1] using And.intro hn hq.2.2.2)
    exact ⟨true,A,hA⟩

end CalderonN.FixedTube
