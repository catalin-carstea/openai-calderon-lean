module

public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Topology.MetricSpace.Pseudo.Lemmas

import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

@[expose] public section

noncomputable section
open Set Filter
open scoped Topology

namespace CalderonN

/-- The scalar profile ℓδ in the shrinking radii of Section 4.2. -/
def softplus (δ t : ℝ) : ℝ :=
  δ * Real.log (1 + Real.exp (t / δ))

private theorem log_one_add_exp_pos (t : ℝ) : 0 < Real.log (1 + Real.exp t) :=
  Real.log_pos (lt_add_of_pos_right 1 (Real.exp_pos t))

theorem softplus_pos {δ : ℝ} (hδ : 0 < δ) (t : ℝ) : 0 < softplus δ t :=
  mul_pos hδ (log_one_add_exp_pos (t / δ))

private theorem softplus_eq_add_reflect {δ : ℝ} (hδ : 0 < δ) (t : ℝ) :
    softplus δ t = t + softplus δ (-t) := by
  have hexp : Real.exp (t / δ) * Real.exp (-t / δ) = 1 := by
    rw [← Real.exp_add, neg_div, add_neg_cancel, Real.exp_zero]
  have hfactor : 1 + Real.exp (t / δ) =
      Real.exp (t / δ) * (1 + Real.exp (-t / δ)) := by
    rw [mul_add, mul_one, hexp, add_comm]
  unfold softplus
  rw [hfactor, Real.log_mul (Real.exp_ne_zero _) (by positivity), Real.log_exp, mul_add]
  rw [mul_div_cancel₀ _ hδ.ne']

/-- The uniform error to the limiting positive part is at most δ log 2. -/
theorem softplus_sub_max_bounds {δ : ℝ} (hδ : 0 < δ) (t : ℝ) :
    0 ≤ softplus δ t - max t 0 ∧ softplus δ t - max t 0 ≤ δ * Real.log 2 := by
  have bound (s : ℝ) (hs : s ≤ 0) : softplus δ s ≤ δ * Real.log 2 := by
    apply mul_le_mul_of_nonneg_left _ hδ.le
    apply Real.log_le_log (by positivity)
    have he := Real.exp_le_one_iff.mpr (div_nonpos_of_nonpos_of_nonneg hs hδ.le)
    linarith
  by_cases ht : t ≤ 0
  · rw [max_eq_right ht, sub_zero]
    exact ⟨(softplus_pos hδ t).le, bound t ht⟩
  · have ht' : 0 ≤ t := le_of_not_ge ht
    rw [max_eq_left ht', softplus_eq_add_reflect hδ t, add_sub_cancel_left]
    exact ⟨(softplus_pos hδ (-t)).le, bound (-t) (neg_nonpos.mpr ht')⟩

theorem tendsto_softplus (t : ℝ) :
    Tendsto (fun δ => softplus δ t) (𝓝[Ioc (0 : ℝ) 1] 0) (𝓝 (max t 0)) := by
  have hError : Tendsto (fun δ => softplus δ t - max t 0) (𝓝[Ioc (0 : ℝ) 1] 0) (𝓝 0) := by
    have hδ : ∀ᶠ δ in 𝓝[Ioc (0 : ℝ) 1] 0, δ ∈ Ioc (0 : ℝ) 1 := eventually_mem_nhdsWithin
    apply squeeze_zero' (hδ.mono fun δ hδ => (softplus_sub_max_bounds hδ.1 t).1)
      (hδ.mono fun δ hδ => (softplus_sub_max_bounds hδ.1 t).2)
    have htend : Tendsto (fun δ : ℝ => δ) (𝓝[Ioc (0 : ℝ) 1] 0) (𝓝 0) :=
      tendsto_nhdsWithin_of_tendsto_nhds continuousAt_id
    simpa only [zero_mul] using htend.mul_const (Real.log 2)
  simpa only [sub_add_cancel, zero_add] using hError.add_const (max t 0)

theorem hasDerivAt_softplus {δ : ℝ} (hδ : δ ≠ 0) (t : ℝ) :
    HasDerivAt (softplus δ) (Real.exp (t / δ) / (1 + Real.exp (t / δ))) t := by
  have hexp := ((hasDerivAt_id' t).div_const δ).exp
  have hsum := (hasDerivAt_const t (1 : ℝ)).add hexp
  have hlog := hsum.log (show 1 + Real.exp (t / δ) ≠ 0 by positivity)
  convert hlog.const_mul δ using 1
  · rfl
  · simp only [Pi.add_apply, zero_add, one_div]
    field_simp [hδ]

private theorem scale_deriv_pos (s : ℝ) :
    0 < Real.log (1 + Real.exp s) - s * Real.exp s / (1 + Real.exp s) := by
  by_cases hs : s ≤ 0
  · exact sub_pos.mpr ((div_nonpos_of_nonpos_of_nonneg
      (mul_nonpos_of_nonpos_of_nonneg hs (Real.exp_pos s).le) (by positivity)).trans_lt
      (log_one_add_exp_pos s))
  · have hs' : 0 < s := lt_of_not_ge hs
    have hlt : s < Real.log (1 + Real.exp s) := by
      calc
        s = Real.log (Real.exp s) := (Real.log_exp s).symm
        _ < Real.log (1 + Real.exp s) := Real.log_lt_log (Real.exp_pos s) (by linarith only)
    have hfrac : s * Real.exp s / (1 + Real.exp s) < s := by
      apply (div_lt_iff₀ (by positivity)).2
      rw [mul_add, mul_one]
      linarith
    exact sub_pos.mpr (hfrac.trans hlt)

private theorem hasDerivAt_softplus_scale (t : ℝ) {δ : ℝ} (hδ : 0 < δ) :
    HasDerivAt (fun s => softplus s t)
      (Real.log (1 + Real.exp (t / δ)) -
        (t / δ) * Real.exp (t / δ) / (1 + Real.exp (t / δ))) δ := by
  have hq := (hasDerivAt_const δ t).div (hasDerivAt_id' δ) hδ.ne'
  have hs := (hasDerivAt_const δ (1 : ℝ)).add hq.exp
  have hl := hs.log (show 1 + Real.exp (t / δ) ≠ 0 by positivity)
  convert (hasDerivAt_id' δ).mul hl using 1
  · rfl
  · simp only [Pi.add_apply, Pi.div_apply, zero_mul, one_mul, zero_add, zero_sub]
    field_simp [hδ.ne']
    ring

/-- Moving from a smaller positive δ to a larger δ increases the profile. -/
theorem strictMonoOn_softplus_scale (t : ℝ) :
    StrictMonoOn (fun δ => softplus δ t) (Ioi 0) := by
  apply strictMonoOn_of_deriv_pos (convex_Ioi (0 : ℝ))
  · exact fun δ hδ => (hasDerivAt_softplus_scale t hδ).continuousAt.continuousWithinAt
  · intro δ hδ
    rw [interior_Ioi] at hδ
    rw [(hasDerivAt_softplus_scale t hδ).deriv]
    exact scale_deriv_pos _

theorem lipschitzWith_softplus {δ : ℝ} (hδ : δ ≠ 0) :
    LipschitzWith 1 (softplus δ) := by
  apply lipschitzWith_of_nnnorm_deriv_le (fun t => (hasDerivAt_softplus hδ t).differentiableAt)
  intro t
  rw [(hasDerivAt_softplus hδ t).deriv]
  apply NNReal.coe_le_coe.mp
  simp only [coe_nnnorm, NNReal.coe_one, Real.norm_eq_abs]
  rw [abs_of_pos (by positivity)]
  exact (div_le_one (by positivity)).2 (le_add_of_nonneg_left zero_le_one)

/-- The radius of the normal sphere at each center. -/
def shrinkingRadius {E : Type*} (R : ℝ) (p : ℕ) (depth : E → ℝ) (δ : ℝ) (y : E) : ℝ :=
  R * (softplus δ (depth y)) ^ p

theorem shrinkingRadius_pos {E : Type*} {R δ : ℝ} (hR : 0 < R) (hδ : 0 < δ)
    (p : ℕ) (depth : E → ℝ) (y : E) : 0 < shrinkingRadius R p depth δ y :=
  mul_pos hR (pow_pos (softplus_pos hδ (depth y)) p)

theorem shrinkingRadius_mono {E : Type*} {R : ℝ} (hR : 0 ≤ R)
    (p : ℕ) (depth : E → ℝ) (y : E) :
    MonotoneOn (fun δ => shrinkingRadius R p depth δ y) (Ioi 0) := by
  intro δ hδ δ' hδ' hle
  exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (softplus_pos hδ (depth y)).le
    ((strictMonoOn_softplus_scale (depth y)).monotoneOn hδ hδ' hle) p) hR

theorem shrinkingRadius_continuousOn {E : Type*} [TopologicalSpace E] {K : Set E}
    (R : ℝ) (p : ℕ) {depth : E → ℝ} (hdepth : ContinuousOn depth K) :
    ContinuousOn (Function.uncurry (shrinkingRadius R p depth)) (Ioc (0 : ℝ) 1 ×ˢ K) := by
  have hδ : ContinuousOn Prod.fst (Ioc (0 : ℝ) 1 ×ˢ K) := continuous_fst.continuousOn
  have hdepth' : ContinuousOn (fun q : ℝ × E => depth q.2) (Ioc (0 : ℝ) 1 ×ˢ K) :=
    hdepth.comp continuous_snd.continuousOn fun _ h => h.2
  have harg := hdepth'.div hδ (fun _ h => h.1.1.ne')
  have hsum : ContinuousOn (fun q : ℝ × E => 1 + Real.exp (depth q.2 / q.1))
      (Ioc (0 : ℝ) 1 ×ˢ K) :=
    continuousOn_const.add (Real.continuous_exp.comp_continuousOn harg)
  have hlog := hsum.log fun q _ =>
    (add_pos zero_lt_one (Real.exp_pos (depth q.2 / q.1))).ne'
  exact continuousOn_const.mul ((hδ.mul hlog).pow p)

theorem shrinkingRadius_tendsto_zero {E : Type*} (R : ℝ) {p : ℕ} (hp : p ≠ 0)
    {depth : E → ℝ} {y : E} (hy : depth y ≤ 0) :
    Tendsto (fun δ => shrinkingRadius R p depth δ y) (𝓝[Ioc (0 : ℝ) 1] 0) (𝓝 0) := by
  simpa only [max_eq_right hy, zero_pow hp, mul_zero, shrinkingRadius] using
    ((tendsto_softplus (depth y)).pow p).const_mul R

theorem le_shrinkingRadius {E : Type*} {R δ : ℝ} (hR : 0 ≤ R) (hδ : 0 < δ)
    (p : ℕ) {depth : E → ℝ} {y : E} (hy : 0 ≤ depth y) :
    R * depth y ^ p ≤ shrinkingRadius R p depth δ y := by
  have h := (softplus_sub_max_bounds hδ (depth y)).1
  rw [max_eq_left hy, sub_nonneg] at h
  exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hy h p) hR

/-- The positive regularization parameter is a valid local radius
coordinate at every center. -/
theorem deriv_shrinkingRadius_parameter_pos {Z : Type*} {R δ : ℝ}
    (hR : 0 < R) (hδ : 0 < δ) {p : ℕ} (hp : 0 < p) (depth : Z → ℝ) (y : Z) :
    0 < deriv (fun d => shrinkingRadius R p depth d y) δ := by
  have h := ((hasDerivAt_softplus_scale (depth y) hδ).pow p).const_mul R
  change 0 < deriv (fun d => R * softplus d (depth y)^p) δ
  simp only [Pi.pow_apply] at h
  rw [h.deriv]
  exact mul_pos hR (mul_pos (mul_pos (Nat.cast_pos.mpr hp)
    (pow_pos (softplus_pos hδ (depth y)) _)) (scale_deriv_pos _))

end CalderonN
