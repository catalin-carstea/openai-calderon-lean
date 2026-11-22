module

public import Proof.CalderonN.DilationHarmonic

import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.Calculus.FDeriv.Congr
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity

public section

noncomputable section
open Set Filter
open scoped ContDiff Topology

namespace CalderonN

variable {dim : ℕ} [NeZero dim]

theorem iteratedFDeriv_dilation {Ω : Set (X dim)} (hΩ : IsOpen Ω) {f : (X dim) → ℝ}
    (hf : ContDiffOn ℝ ∞ f Ω) {lam : ℝ} {y : (X dim)} (hy : lam • y ∈ Ω) (m : ℕ) :
    iteratedFDeriv ℝ m (fun z => f (lam • z)) y =
      lam ^ m • iteratedFDeriv ℝ m f (lam • y) := by
  let L : (X dim) →L[ℝ] (X dim) := lam • ContinuousLinearMap.id ℝ (X dim)
  have hU : IsOpen (L ⁻¹' Ω) := hΩ.preimage L.continuous
  have hy' : L y ∈ Ω := hy
  have hc := L.iteratedFDerivWithin_comp_right hf hΩ.uniqueDiffOn hU.uniqueDiffOn hy'
    (i := m) (by simp)
  rw [iteratedFDerivWithin_of_isOpen m hU hy', iteratedFDerivWithin_of_isOpen m hΩ hy'] at hc
  change iteratedFDeriv ℝ m (f ∘ L) y = lam ^ m • iteratedFDeriv ℝ m f (L y)
  rw [hc]
  ext v
  simpa only [ContinuousMultilinearMap.compContinuousLinearMap_apply,
    L, smul_apply, ContinuousLinearMap.id_apply,
    Finset.prod_const, Finset.card_univ, Fintype.card_fin] using
    (iteratedFDeriv ℝ m f (L y)).map_smul_univ (fun _ => lam) v

private theorem iteratedFDeriv_affine_eq_zero (c lam : ℝ) (L : (X dim) →L[ℝ] ℝ)
    (y : (X dim)) {m : ℕ} (hm : 2 ≤ m) :
    iteratedFDeriv ℝ m (fun z => c + lam * L z) y = 0 := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hm
  have heq : fderiv ℝ (fun z : (X dim) => c + lam * L z) = fun _ => lam • L := by
    funext z
    exact (((lam • L).hasFDerivAt (x := z)).const_add c).fderiv
  apply norm_eq_zero.mp
  rw [show 2 + k = (k + 1) + 1 by omega, ← norm_iteratedFDeriv_fderiv, heq,
    iteratedFDeriv_succ_const, Pi.zero_apply, norm_zero]

theorem iteratedFDeriv_renormalizedHarmonic {Ω : Set (X dim)} (hΩ : IsOpen Ω)
    {u : (X dim) → ℝ} (hu : ContDiffOn ℝ ∞ u Ω) (c : ℝ) (L : (X dim) →L[ℝ] ℝ)
    {lam : ℝ} (hlam : lam ≠ 0) {y : (X dim)} (hy : lam • y ∈ Ω) {m : ℕ} (hm : 2 ≤ m) :
    iteratedFDeriv ℝ m (renormalizedHarmonic c L u lam) y =
      lam ^ (m - 2) • iteratedFDeriv ℝ m u (lam • y) := by
  let U := {z : (X dim) | lam • z ∈ Ω}
  have hU : IsOpen U := hΩ.preimage ((lam • ContinuousLinearMap.id ℝ (X dim)).continuous)
  have hu' : ContDiffAt ℝ m (fun z => u (lam • z)) y :=
    ((contDiffOn_dilation hu lam).contDiffAt (hU.mem_nhds hy)).of_le (by simp)
  have hL : ContDiffAt ℝ m (fun z : (X dim) => c + lam * L z) y :=
    (contDiff_const.add ((lam • L).contDiff)).contDiffAt
  change iteratedFDeriv ℝ m (fun z => (lam ^ 2)⁻¹ • (u (lam • z) - (c + lam * L z))) y = _
  rw [iteratedFDeriv_const_smul_apply' (hu'.sub hL), fun_iteratedFDeriv_sub_apply hu' hL,
    iteratedFDeriv_affine_eq_zero c lam L y hm, sub_zero,
    iteratedFDeriv_dilation hΩ hu hy, smul_smul]
  have hexp : m = 2 + (m - 2) := by omega
  conv_lhs => rw [show (lam ^ 2)⁻¹ * lam ^ m = lam ^ (m - 2) by
    nth_rw 1 [hexp]
    rw [pow_add, ← mul_assoc, inv_mul_cancel₀ (pow_ne_zero _ hlam), one_mul]]

/-- One bound at a fixed derivative order of the original functions
controls the entire renormalized family on any fixed compact chart room. -/
theorem exists_uniform_renormalizedHarmonic_jet_bound {Ω K : Set (X dim)} (hΩ : IsOpen Ω)
    (h₀ : (0 : (X dim)) ∈ Ω) (hK : IsCompact K) {n : ℕ} {u : Fin n → (X dim) → ℝ}
    (hu : ∀ a, ContDiffOn ℝ ∞ (u a) Ω) (c : Fin n → ℝ) (L : Fin n → (X dim) →L[ℝ] ℝ)
    {m : ℕ} (hm : 2 ≤ m) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ᶠ lam in 𝓝 (0 : ℝ), 0 < lam → ∀ y ∈ K, lam • y ∈ Ω ∧
      ∀ a, ‖iteratedFDeriv ℝ m (renormalizedHarmonic (c a) (L a) (u a) lam) y‖ ≤ C := by
  obtain ⟨ρ, hρ, hρΩ⟩ := Metric.mem_nhds_iff.mp (hΩ.mem_nhds h₀)
  let B := Metric.closedBall (0 : (X dim)) (ρ / 2)
  have hBΩ : B ⊆ Ω := (Metric.closedBall_subset_ball (by linarith)).trans hρΩ
  have hbound (a : Fin n) : ∃ M : ℝ, 0 ≤ M ∧ ∀ z ∈ B, ‖iteratedFDeriv ℝ m (u a) z‖ ≤ M := by
    have hc : ContinuousOn (iteratedFDeriv ℝ m (u a)) B := fun z hz =>
      (((hu a).contDiffAt (hΩ.mem_nhds (hBΩ hz))).continuousAt_iteratedFDeriv (by simp)).continuousWithinAt
    obtain ⟨M, hM⟩ := (isCompact_closedBall _ _).exists_bound_of_continuousOn hc
    exact ⟨max M 0, le_max_right _ _, fun z hz => (hM z hz).trans (le_max_left _ _)⟩
  choose M hMpos hM using hbound
  let C : ℝ := 1 + ∑ a, M a
  refine ⟨C, le_add_of_nonneg_right (Finset.sum_nonneg fun a _ => hMpos a), ?_⟩
  have hnear : ∀ᶠ lam in 𝓝 (0 : ℝ), ∀ y ∈ K, lam • y ∈ Metric.ball 0 (ρ / 2) := by
    apply hK.eventually_forall_of_forall_eventually
    intro y _
    have hmap : Continuous (fun q : ℝ × (X dim) => q.1 • q.2) := continuous_fst.smul continuous_snd
    apply hmap.continuousAt.preimage_mem_nhds
    simpa only [zero_smul] using Metric.ball_mem_nhds (0 : (X dim)) (by positivity : 0 < ρ / 2)
  filter_upwards [hnear, Iio_mem_nhds (zero_lt_one : (0 : ℝ) < 1)] with lam hlam h₁ hpos y hy
  have hyB : lam • y ∈ B := Metric.ball_subset_closedBall (hlam y hy)
  refine ⟨hBΩ hyB, fun a => ?_⟩
  have hb := hM a (lam • y) hyB
  have hpow : lam ^ (m - 2) ≤ 1 := pow_le_one₀ hpos.le (le_of_lt h₁)
  rw [iteratedFDeriv_renormalizedHarmonic hΩ (hu a) _ _ hpos.ne' (hBΩ hyB) hm,
    norm_smul, Real.norm_of_nonneg (pow_nonneg hpos.le _)]
  calc
    _ ≤ 1 * ‖iteratedFDeriv ℝ m (u a) (lam • y)‖ :=
      mul_le_mul_of_nonneg_right hpow (norm_nonneg _)
    _ ≤ M a := by simpa only [one_mul] using hb
    _ ≤ ∑ b, M b := Finset.single_le_sum (fun b _ => hMpos b) (Finset.mem_univ a)
    _ ≤ C := le_add_of_nonneg_left zero_le_one

end CalderonN
