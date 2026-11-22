module

public import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Tactic

public section

noncomputable section
open Set Filter
open scoped ContDiff Topology
open Metric

namespace CalderonN

private def transverseScale {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    (s : ℝ) : P × ℝ →L[ℝ] P × ℝ :=
  (ContinuousLinearMap.fst ℝ P ℝ).prod (s⁻¹ • ContinuousLinearMap.snd ℝ P ℝ)

private theorem transverseScale_norm_le {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    {s : ℝ} (hs : 0 < s) (h1 : s ≤ 1) :
    ‖transverseScale (P := P) s‖ ≤ s⁻¹ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (inv_nonneg.2 hs.le)
  intro p
  change ‖(p.1,s⁻¹ • p.2)‖ ≤ s⁻¹ * ‖p‖
  rw [Prod.norm_def]
  apply max_le
  · have hs' : 1 ≤ s⁻¹ := (one_le_inv₀ hs).mpr h1
    exact (norm_fst_le p).trans (by simpa using mul_le_mul_of_nonneg_right hs' (norm_nonneg p))
  · rw [norm_smul,Real.norm_of_nonneg (inv_nonneg.2 hs.le)]
    exact mul_le_mul_of_nonneg_left (norm_snd_le p) (inv_nonneg.2 hs.le)

private theorem norm_iteratedFDeriv_scale_transverse
    {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    {f : P × ℝ → ℝ} (hf : ContDiff ℝ ∞ f)
    {s : ℝ} (hs : 0 < s) (h1 : s ≤ 1) (n k : ℕ) (q : P × ℝ) :
    ‖iteratedFDeriv ℝ k (fun u : P × ℝ => s^n * f (transverseScale s u)) q‖ ≤
      (s^n * (s⁻¹)^k) * ‖iteratedFDeriv ℝ k f (transverseScale s q)‖ := by
  let A : P × ℝ →L[ℝ] P × ℝ := transverseScale s
  have hsm : ContDiff ℝ ∞ (f ∘ A) := hf.comp A.contDiff
  change ‖iteratedFDeriv ℝ k (s^n • (f ∘ A)) q‖ ≤ _
  rw [iteratedFDeriv_const_smul_apply ((hsm.of_le (by simp)).contDiffAt),norm_smul,
    Real.norm_of_nonneg (pow_nonneg hs.le _),
    A.iteratedFDeriv_comp_right hf _ (by simp)]
  have hb := (iteratedFDeriv ℝ k f (A q)).norm_compContinuousLinearMap_le (fun _ => A)
  simp only [Finset.prod_const,Finset.card_univ,Fintype.card_fin] at hb
  have hNorm : ‖A‖ ≤ s⁻¹ := transverseScale_norm_le (P := P) hs h1
  have hPow : ‖A‖ ^ k ≤ (s⁻¹)^k := pow_le_pow_left₀ (norm_nonneg A) hNorm k
  refine (mul_le_mul_of_nonneg_left
    (hb.trans (mul_le_mul_of_nonneg_left hPow (norm_nonneg _))) (pow_nonneg hs.le n)).trans_eq ?_
  change s^n * (‖iteratedFDeriv ℝ k f (A q)‖ * (s⁻¹)^k) =
    (s^n * (s⁻¹)^k) * ‖iteratedFDeriv ℝ k f (A q)‖
  ring

private theorem hasCompactSupport_transverse_product
    {P : Type*} [TopologicalSpace P] [T2Space P]
    {f : P → ℝ} (hf : HasCompactSupport f) {g : ℝ → ℝ} (hg : HasCompactSupport g) :
    HasCompactSupport (fun q : P × ℝ => f q.1 * g q.2) := by
  apply (hf.isCompact.prod hg.isCompact).of_isClosed_subset (isClosed_tsupport _)
  apply closure_minimal _ (isClosed_tsupport _ |>.prod (isClosed_tsupport _))
  intro q hq
  have h : f q.1 * g q.2 ≠ 0 := hq
  exact ⟨subset_closure (left_ne_zero_of_mul h),subset_closure (right_ne_zero_of_mul h)⟩

/-- A vertical jet of an ambient function agrees with the ordinary
one-variable derivative on the line normal to the parameter plane. -/
theorem iteratedDeriv_transverse_eq
    {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    {f : P × ℝ → ℝ} (hf : ContDiff ℝ ∞ f) (p : P) (k : ℕ) :
    iteratedDeriv k (fun t => f (p,t)) 0 =
      iteratedFDeriv ℝ k f (p,0) (fun _ => (0,1)) := by
  let A := ContinuousLinearMap.inr ℝ P ℝ
  let F (q : P × ℝ) := f ((p,0)+q)
  have hF : ContDiff ℝ ∞ F := hf.comp (contDiff_const.add contDiff_id)
  have hLine : (fun t : ℝ => f (p,t)) = F ∘ A := by
    funext t
    simp [F,A]
  rw [hLine,iteratedDeriv,A.iteratedFDeriv_comp_right hF 0 (by simp),map_zero]
  have hT : iteratedFDeriv ℝ k F 0 = iteratedFDeriv ℝ k f (p,0) := by
    simpa only [F,add_zero] using (iteratedFDeriv_comp_add_left k (p,(0:ℝ)) (0 : P × ℝ) (f := f))
  rw [hT]
  simp [A]

set_option maxHeartbeats 1600000 in
/-- Smooth prescribed normal jets with smoothly varying parameters.
Each compactly supported jet is multiplied by its Taylor monomial and
a cutoff whose radius is chosen to make all lower derivative sums converge. -/
theorem exists_smooth_realization_of_transverse_jets
    {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    (a : ℕ → P → ℝ) (ha : ∀ k, ContDiff ℝ ∞ (a k))
    (hc : ∀ k, HasCompactSupport (a k)) :
    ∃ U : P × ℝ → ℝ, ContDiff ℝ ∞ U ∧
      ∀ (k : ℕ) (p : P), iteratedDeriv k (fun t => U (p,t)) 0 = a k p := by
  classical
  let χ : ContDiffBump (0 : ℝ) :=
    { rIn := 1, rOut := 2, rIn_pos := one_pos, rIn_lt_rOut := by norm_num }
  let g (n : ℕ) (t : ℝ) := (t^n / (n.factorial : ℝ)) * χ t
  let V (n : ℕ) (p : P × ℝ) := a n p.1 * g n p.2
  have hg (n : ℕ) : ContDiff ℝ ∞ (g n) :=
    ((contDiff_id.pow n).div_const _).mul χ.contDiff
  have hgK (n : ℕ) : HasCompactSupport (g n) := χ.hasCompactSupport.mul_left
  have hV (n : ℕ) : ContDiff ℝ ∞ (V n) :=
    ((ha n).comp contDiff_fst).mul ((hg n).comp contDiff_snd)
  have hVK (n : ℕ) : HasCompactSupport (V n) :=
    hasCompactSupport_transverse_product (hc n) (hgK n)
  choose C hC₀ hC using fun n : ℕ => (hVK n).exists_bound_iteratedFDeriv (hV n) n
  choose D hD₀ hD using fun k n : ℕ => (hVK n).exists_bound_iteratedFDeriv (hV n) k
  let r (n : ℕ) : ℝ := min 1 ((1/2:ℝ)^n / (C n+1))
  have hr (n : ℕ) : 0 < r n := lt_min one_pos (div_pos (by positivity) (by linarith [hC₀ n]))
  have hr₁ (n : ℕ) : r n ≤ 1 := min_le_left _ _
  let U (n : ℕ) (q : P × ℝ) := (r n)^n * V n (transverseScale (r n) q)
  have hU (n : ℕ) : ContDiff ℝ ∞ (U n) :=
    contDiff_const.mul ((hV n).comp (transverseScale (P := P) (r n)).contDiff)
  have hscale (n k : ℕ) (q : P × ℝ) :
      ‖iteratedFDeriv ℝ k (U n) q‖ ≤
        ((r n)^n * ((r n)⁻¹)^k) *
          ‖iteratedFDeriv ℝ k (V n) (transverseScale (r n) q)‖ :=
    norm_iteratedFDeriv_scale_transverse (hV n) (hr n) (hr₁ n) n k q
  have htail (k n : ℕ) (hk : k < n) (q : P × ℝ) :
      ‖iteratedFDeriv ℝ k (U n) q‖ ≤ (1/2:ℝ)^n := by
    have hpow : (r n)^n * ((r n)⁻¹)^k = (r n)^(n-k) := by
      rw [inv_pow,← pow_sub₀ (r n) (hr n).ne' hk.le]
    have hs : (r n)^(n-k) ≤ r n := by
      simpa only [pow_one] using pow_le_pow_of_le_one (hr n).le (hr₁ n) (show 1 ≤ n-k by omega)
    have hh : r n * (C n+1) ≤ (1/2:ℝ)^n :=
      (le_div_iff₀ (by linarith [hC₀ n] : 0 < C n+1)).mp (min_le_right _ _)
    refine (hscale n k q).trans ?_
    rw [hpow]
    calc
      _ ≤ (r n)^(n-k) * C n := mul_le_mul_of_nonneg_left (hC n k hk.le _) (pow_nonneg (hr n).le _)
      _ ≤ r n * C n := mul_le_mul_of_nonneg_right hs (hC₀ n)
      _ ≤ r n * (C n+1) := mul_le_mul_of_nonneg_left (by linarith) (hr n).le
      _ ≤ _ := hh
  let b (k n : ℕ) : ℝ := if k < n then (1/2:ℝ)^n else
    ((r n)^n * ((r n)⁻¹)^k) * D k n
  have hSumm (k : ℕ) : Summable (b k) := by
    refine Summable.of_norm_bounded_eventually
      (summable_geometric_of_norm_lt_one (by norm_num : ‖(1/2:ℝ)‖ < 1)) ?_
    rw [Nat.cofinite_eq_atTop]
    filter_upwards [eventually_gt_atTop k] with n hn
    simp [b,hn]
  have hb (k n : ℕ) (q : P × ℝ) : ‖iteratedFDeriv ℝ k (U n) q‖ ≤ b k n := by
    by_cases hk : k < n
    · simpa only [b,ite_eq_left hk] using htail k n hk q
    · simpa only [b,ite_eq_right hk] using (hscale n k q).trans
        (mul_le_mul_of_nonneg_left (hD k n k le_rfl _)
          (mul_nonneg (pow_nonneg (hr n).le n) (pow_nonneg (inv_nonneg.2 (hr n).le) k)))
  have hJ (n k : ℕ) (p : P) :
      iteratedFDeriv ℝ k (U n) (p,0) (fun _ => (0,1)) = if k = n then a n p else 0 := by
    have he :
        (fun t : ℝ => U n (p,t)) =ᶠ[𝓝 (0 : ℝ)] fun t => (a n p / (n.factorial : ℝ)) * t^n := by
      have hmap : Continuous (fun t : ℝ => (r n)⁻¹ * t) := continuous_const.mul continuous_id
      have ht : ∀ᶠ t in 𝓝 (0 : ℝ), (r n)⁻¹ * t ∈ closedBall (0 : ℝ) 1 := by
        apply hmap.continuousAt.preimage_mem_nhds
        simpa only [mul_zero] using closedBall_mem_nhds (0 : ℝ) one_pos
      filter_upwards [ht] with t ht
      have hχ : χ ((r n)⁻¹ * t) = 1 := χ.one_of_mem_closedBall ht
      change (r n)^n * (a n p * ((((r n)⁻¹ * t)^n / (n.factorial : ℝ)) *
        χ ((r n)⁻¹ * t))) = (a n p / (n.factorial : ℝ)) * t^n
      rw [hχ,mul_one,mul_pow,inv_pow]
      field_simp [pow_ne_zero n (hr n).ne']
    rw [← iteratedDeriv_transverse_eq (hU n),he.iteratedDeriv_eq k,iteratedDeriv_const_mul_field,
      iteratedDeriv_fun_pow_zero]
    by_cases h : k = n
    · subst k
      simp only [ite_true]
      exact div_mul_cancel₀ _ (by exact_mod_cast Nat.factorial_ne_zero n)
    · simp [h]
  let F (q : P × ℝ) := ∑' n, U n q
  have hF : ContDiff ℝ ∞ F :=
    contDiff_tsum hU (fun k _ => hSumm k) (fun k n q _ => hb k n q)
  refine ⟨F,hF,fun k p => ?_⟩
  rw [iteratedDeriv_transverse_eq hF]
  change iteratedFDeriv ℝ k (fun q => ∑' n, U n q) (p,0) (fun _ => (0,1)) = _
  rw [iteratedFDeriv_tsum_apply hU (fun j _ => hSumm j) (fun j n q _ => hb j n q) (by simp)]
  let E := ContinuousMultilinearMap.apply ℝ (fun _ : Fin k => P × ℝ) ℝ
    (fun _ => (0,1))
  have hSum : Summable (fun n => iteratedFDeriv ℝ k (U n) (p,0)) :=
    Summable.of_norm_bounded (hSumm k) (fun n => hb k n (p,0))
  change E (∑' n, iteratedFDeriv ℝ k (U n) (p,0)) = _
  rw [E.map_tsum hSum]
  change (∑' n, iteratedFDeriv ℝ k (U n) (p,0) (fun _ => (0,1))) = _
  simp_rw [hJ]
  rw [tsum_eq_single k]
  · simp
  · intro n hn
    simp [Ne.symm hn]

end CalderonN
