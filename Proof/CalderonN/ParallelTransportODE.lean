module

public import Proof.CalderonN.ParallelFrameCalculus

import Proof.LocalMetricExtension.ODE.Analysis.ODE.InitialCondition
import Proof.CalderonN.CovariantHessian
import Mathlib.Analysis.Calculus.ContDiff.WithLp
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Tactic

@[expose] public section

noncomputable section
open Set Metric Filter
open scoped ContDiff NNReal Topology

namespace CalderonN

variable {dim : ℕ} [NeZero dim]

/-- A smooth time-dependent field with linear growth on the time interval
has a smooth solution on the whole interval through any prescribed initial value. -/
theorem exists_smooth_solution_of_linearGrowth
    {f : ℝ × (X dim) → (X dim)} (hf : ContDiff ℝ ∞ f)
    {K : ℝ} (hK : 0 ≤ K)
    (hgrowth : ∀ t ∈ Icc (0 : ℝ) 1, ∀ w, ‖f (t,w)‖ ≤ K * ‖w‖)
    (w₀ : (X dim)) : ∃ w : ℝ → (X dim), ContDiff ℝ ∞ w ∧ w 0 = w₀ ∧
      ∀ t ∈ Icc (0 : ℝ) 1, ∀ᶠ s in 𝓝 t, HasDerivAt w (f (s,w s)) s := by
  let R := 2 + ‖w₀‖ * Real.exp K
  have hR : 0 < R := by dsimp [R]; positivity
  let χ : ContDiffBump (0 : ℝ × (X dim)) := ⟨R,R+1,hR,lt_add_one R⟩
  let F : ℝ × (X dim) → (X dim) := fun q => χ q • f q
  have hF : ContDiff ℝ ∞ F := χ.contDiff.smul hf
  obtain ⟨L,hL⟩ := hF.lipschitzWith_of_hasCompactSupport χ.hasCompactSupport.smul_right (by simp)
  let V : ℝ × (X dim) → (ℝ × (X dim)) := fun q => (1,F q)
  have hV : LipschitzWith L V := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    rw [Prod.dist_eq]
    exact max_le (by simpa [V] using mul_nonneg L.coe_nonneg dist_nonneg) (hL.dist_le_mul x y)
  let u := ODE.globalSolution V hV (0,w₀)
  have huD (t : ℝ) : HasDerivAt u (V (u t)) t := ODE.hasDerivAt_globalSolution V hV (0,w₀) t
  have hu₀ : u 0 = (0,w₀) := ODE.globalSolution_zero V hV (0,w₀)
  have ht (t : ℝ) : (u t).1 = t := by
    have hz (s : ℝ) : HasDerivAt (fun a => (u a).1-a) 0 s := by
      have h : HasDerivAt (fun a => (u a).1) 1 s :=
        (ContinuousLinearMap.fst ℝ ℝ (X dim)).hasFDerivAt.comp_hasDerivAt s (huD s)
      convert h.sub (hasDerivAt_id s) using 1
      all_goals first | rfl | norm_num
    have he := is_const_of_deriv_eq_zero (fun s => (hz s).differentiableAt)
      (fun s => (hz s).deriv) t 0
    simpa [hu₀,sub_eq_zero] using he
  let w (t : ℝ) := (u t).2
  have hw₀ : w 0 = w₀ := congrArg Prod.snd hu₀
  have huSmooth : ContDiff ℝ ∞ u := by
    apply contDiff_iff_forall_nat_le.mpr
    intro n _
    exact ((ODE.contDiff_globalSolution n V hV
      ((contDiff_const.prodMk hF).of_le (by simp))).comp
        (contDiff_const.prodMk contDiff_id)).of_le (by exact_mod_cast Nat.le_succ n)
  have hw : ContDiff ℝ ∞ w := huSmooth.snd
  have hwD (t : ℝ) : HasDerivAt w (F (t,w t)) t := by
    have e : u t = (t,w t) := Prod.ext (ht t) rfl
    have h := (ContinuousLinearMap.snd ℝ ℝ (X dim)).hasFDerivAt.comp_hasDerivAt t (huD t)
    change HasDerivAt w (F (u t)) t at h
    simpa only [e] using h
  have hb (t : ℝ) (ht : t ∈ Ico (0 : ℝ) 1) : ‖F (t,w t)‖ ≤ K * ‖w t‖ + 0 := by
    rw [add_zero,show F (t,w t) = χ (t,w t) • f (t,w t) from rfl,
      norm_smul,Real.norm_of_nonneg χ.nonneg]
    exact (mul_le_of_le_one_left (norm_nonneg _) χ.le_one).trans
      (hgrowth t (Ico_subset_Icc_self ht) _)
  have hnorm (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      ‖w t‖ ≤ ‖w₀‖ * Real.exp K := by
    have h := norm_le_gronwallBound_of_norm_deriv_right_le hw.continuous.continuousOn
      (fun s _ => (hwD s).hasDerivWithinAt) (le_of_eq (congrArg norm hw₀)) hb t ht
    rw [gronwallBound_ε0,sub_zero] at h
    exact h.trans (mul_le_mul_of_nonneg_left
      (Real.exp_le_exp.mpr (mul_le_of_le_one_right hK ht.2)) (norm_nonneg _))
  refine ⟨w,hw,hw₀,fun t ht => ?_⟩
  have hm : (t,w t) ∈ ball (0 : ℝ × (X dim)) R := by
    rw [mem_ball_zero_iff,Prod.norm_def,max_lt_iff,Real.norm_of_nonneg ht.1]
    exact ⟨ht.2.trans_lt (by dsimp [R]; linarith [show 0 ≤ ‖w₀‖ * Real.exp K by positivity]),
      (hnorm t ht).trans_lt (by dsimp [R]; linarith)⟩
  have he : ∀ᶠ s in 𝓝 t, (s,w s) ∈ ball (0 : ℝ × (X dim)) R :=
    (continuous_id.prodMk hw.continuous).continuousAt.eventually (isOpen_ball.mem_nhds hm)
  filter_upwards [he] with s hs
  have hχ : χ (s,w s) = 1 := χ.one_of_mem_closedBall (ball_subset_closedBall hs)
  simpa only [F,hχ,one_smul] using hwD s

/-- Parallel transport along a smooth chart curve exists for the full
geodesic interval and preserves the initial frame's Gram matrix. -/
theorem exists_parallelFrame {g : (MetricField dim)} (hg : SmoothMetric univ g)
    {q : ℝ → (X dim)} (hq : ContDiff ℝ ∞ q) (e : (I dim) → (X dim)) :
    ∃ F : ℝ → (I dim) → (X dim), (∀ i, ContDiff ℝ ∞ (fun t => F t i)) ∧
      (∀ i, F 0 i = e i) ∧
      ∀ t ∈ Icc (0 : ℝ) 1, ∀ᶠ s in 𝓝 t,
        (∀ i, HasDerivAt (fun r => F r i)
          (-connection g (q s) (deriv q s) (F s i)) s) ∧
        ∀ i j, metricPair g (q s) (F s i) (F s j) = metricPair g (q 0) (e i) (e j) := by
  let A (t : ℝ) (j : (I dim)) : (X dim) := WithLp.toLp 2 fun k =>
    ∑ i, christoffel g (q t) k i j * deriv q t i
  have hV : ContDiff ℝ ∞ (deriv q) := (hq.of_le (show ∞ + 1 ≤ ∞ by simp)).deriv'
  have hA (j : (I dim)) : ContDiff ℝ ∞ (fun t => A t j) := by
    rw [← contDiffOn_univ]
    apply (contDiffOn_piLp 2).mpr
    intro k
    change ContDiffOn ℝ ∞ (fun t => ∑ i, christoffel g (q t) k i j * deriv q t i) univ
    apply ContDiffOn.sum
    intro i _
    exact (((contDiffOn_univ.mp (contDiffOn_christoffel isOpen_univ hg k i j)).comp hq).mul
      ((EuclideanSpace.proj i : (X dim) →L[ℝ] ℝ).contDiff.comp hV)).contDiffOn
  choose B hB using fun j => (isCompact_Icc (a := (0 : ℝ)) (b := 1)).exists_bound_of_continuousOn
    (hA j).continuous.continuousOn
  let f (p : ℝ × (X dim)) : (X dim) := -∑ j, p.2 j • A p.1 j
  have hf : ContDiff ℝ ∞ f := by
    apply ContDiff.neg
    exact ContDiff.sum fun j _ =>
      ((EuclideanSpace.proj j : (X dim) →L[ℝ] ℝ).contDiff.comp contDiff_snd).smul ((hA j).comp contDiff_fst)
  have hfEq (t : ℝ) (w : (X dim)) : f (t,w) = -connection g (q t) (deriv q t) w := by
    rw [neg_inj]
    ext k
    change (EuclideanSpace.proj (𝕜 := ℝ) k) (∑ j, w j • A t j) =
      ∑ i, ∑ j, christoffel g (q t) k i j * deriv q t i * w j
    have hk (j : I dim) : EuclideanSpace.proj (𝕜 := ℝ) k (A t j) =
        ∑ i, christoffel g (q t) k i j * deriv q t i := rfl
    simp only [map_sum, map_smul, hk, smul_eq_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  let K : ℝ := ∑ j, max (B j) 0
  have hK : 0 ≤ K := Finset.sum_nonneg fun _ _ => le_max_right _ _
  have hgrowth (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) (w : (X dim)) : ‖f (t,w)‖ ≤ K * ‖w‖ := by
    change ‖-∑ j, w j • A t j‖ ≤ _
    rw [norm_neg,Finset.sum_mul]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j hj => ?_)
    rw [norm_smul,mul_comm]
    exact mul_le_mul ((hB j t ht).trans (le_max_left _ _)) (PiLp.norm_apply_le w j)
      (norm_nonneg _) (le_max_right _ _)
  choose u hu hs hD using fun i => exists_smooth_solution_of_linearGrowth hf hK hgrowth (e i)
  let F (t : ℝ) (i : (I dim)) := u i t
  have hF (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : ∀ᶠ s in 𝓝 t, ∀ i,
      HasDerivAt (fun r => F r i) (-connection g (q s) (deriv q s) (F s i)) s := by
    apply Filter.eventually_all.mpr
    intro i
    simpa only [F,hfEq] using hD i t ht
  have hqD (s : ℝ) : HasDerivAt q (deriv q s) s :=
    (hq.differentiable (by simp) s).hasDerivAt
  have hGram (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) (i j : (I dim)) :
      metricPair g (q t) (F t i) (F t j) = metricPair g (q 0) (e i) (e j) := by
    simpa only [show ∀ i, F 0 i = e i from hs] using
      parallelFrame_metricPair_eq_initial isOpen_univ hg (deriv q) F
        (fun s _ => ⟨mem_univ _,hqD s⟩) (fun s h => (hF s h).self_of_nhds) ht i j
  refine ⟨F,hu,hs,fun t ht => ?_⟩
  obtain ⟨δ,hδ,hball⟩ := Metric.mem_nhds_iff.mp (hF t ht)
  filter_upwards [isOpen_ball.mem_nhds (mem_ball_self hδ)] with s hs'
  refine ⟨hball hs',fun i j => ?_⟩
  let P (r : ℝ) := metricPair g (q r) (F r i) (F r j)
  have hP (r : ℝ) (hr : r ∈ ball t δ) : HasDerivAt P 0 r := by
    simpa [P,metricPair] using hasDerivAt_metricPair isOpen_univ hg (mem_univ (q r)) (hqD r)
      (hball hr i) (hball hr j)
  have he := isOpen_ball.is_const_of_deriv_eq_zero (convex_ball t δ).isPreconnected
    (fun r hr => (hP r hr).differentiableAt.differentiableWithinAt)
    (fun r hr => (hP r hr).deriv) hs' (mem_ball_self hδ)
  exact he.trans (hGram t ht i j)

/-- The variation has smooth coordinates in any chosen parallel frame
along the base path, including on time neighborhoods of its endpoints. -/
theorem framed_variation_of_parallelFrame {g : (MetricField dim)} (hg : SmoothMetric univ g)
    {q : ℝ × ℝ → (X dim)} (hq : ContDiff ℝ ∞ q)
    (F : ℝ → (I dim) → (X dim)) (hF : ∀ i, ContDiff ℝ ∞ (fun t => F t i))
    (hD : ∀ t ∈ Icc (0 : ℝ) 1, ∀ᶠ s in 𝓝 t,
      (∀ i, HasDerivAt (fun r => F r i)
        (-connection g (q (0,s)) (timeVelocity q (0,s)) (F s i)) s) ∧
      ∀ i j, metricPair g (q (0,s)) (F s i) (F s j) = if i = j then 1 else 0) :
    let Z (s : ℝ) := frameCoordinates g (q (0,s)) (F s) (pathVariation q (0,s))
    ContDiff ℝ ∞ Z ∧
    ∀ t ∈ Icc (0 : ℝ) 1, ∀ᶠ s in 𝓝 t,
      (∀ i, HasDerivAt (fun r => F r i)
        (-connection g (q (0,s)) (timeVelocity q (0,s)) (F s i)) s) ∧
      pathVariation q (0,s) = ∑ i, Z s i • F s i := by
  let a (s : ℝ) := q (0,s)
  let J (s : ℝ) := pathVariation q (0,s)
  have hslice : ContDiff ℝ ∞ (fun s : ℝ => ((0 : ℝ),s)) :=
    contDiff_const.prodMk contDiff_id
  have ha : ContDiff ℝ ∞ a := hq.comp hslice
  have hJ : ContDiff ℝ ∞ J := (contDiff_pathVariation hq).comp hslice
  let Z (s : ℝ) := frameCoordinates g (a s) (F s) (J s)
  have hproj (i : (I dim)) : ContDiff ℝ ∞ (fun s => J s i) :=
    (EuclideanSpace.proj i : (X dim) →L[ℝ] ℝ).contDiff.comp hJ
  have hZ : ContDiff ℝ ∞ Z := by
    rw [← contDiffOn_univ]
    apply (contDiffOn_piLp 2).mpr
    intro i
    change ContDiffOn ℝ ∞ (fun s => metricPair g (a s) (J s) (F s i)) univ
    unfold metricPair
    exact ContDiffOn.sum fun j _ => ContDiffOn.sum fun k _ =>
      ((((contDiffOn_univ.mp (hg.1 j k)).comp ha).mul (hproj j)).mul
        ((EuclideanSpace.proj k : (X dim) →L[ℝ] ℝ).contDiff.comp (hF i))).contDiffOn
  refine ⟨hZ,fun t ht => ?_⟩
  filter_upwards [hD t ht] with s hs
  exact ⟨hs.1,(frameVector_frameCoordinates g (a s) (J s) (F s) hs.2).symm⟩

end CalderonN
