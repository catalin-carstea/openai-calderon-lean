module

public import Proof.CalderonN.Chart

import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.FDeriv.Congr

public section

open Set Filter
open scoped BigOperators ContDiff Topology

namespace CalderonN

variable {dim : ℕ} [NeZero dim]

/-- Spatial derivatives of a slice are bounded by the joint derivatives.
Adapted from `Calderon/SpatialSourceJetRecoveryBounds.lean`. -/
theorem norm_iteratedFDeriv_slice_le {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {U : Set (ℝ × (X dim))} (hU : IsOpen U) {f : ℝ × (X dim) → V} (hf : ContDiffOn ℝ ∞ f U)
    {lam : ℝ} {y : (X dim)} (hy : (lam, y) ∈ U) (n : ℕ) :
    ‖iteratedFDeriv ℝ n (fun z => f (lam, z)) y‖ ≤ ‖iteratedFDeriv ℝ n f (lam, y)‖ := by
  let b : ℝ × (X dim) := (lam, 0)
  let g : (X dim) →ₗᵢ[ℝ] ℝ × (X dim) := LinearIsometry.inr ℝ ℝ (X dim)
  let l := g.toContinuousLinearMap
  let H : ℝ × (X dim) → V := fun z => f (z + b)
  let S : Set (ℝ × (X dim)) := (fun z => z + b) ⁻¹' U
  have hS : IsOpen S := hU.preimage (continuous_id.add continuous_const)
  have hH : ContDiffOn ℝ ∞ H S :=
    hf.comp (contDiff_id.add contDiff_const).contDiffOn (fun _ hz => hz)
  have hPre : IsOpen (l ⁻¹' S) := hS.preimage l.continuous
  have hl : l y ∈ S := by simpa [S, l, g, b] using hy
  have hh := l.iteratedFDerivWithin_comp_right hH hS.uniqueDiffOn hPre.uniqueDiffOn hl
    (i := n) (by simp)
  rw [iteratedFDerivWithin_of_isOpen n hPre hl, iteratedFDerivWithin_of_isOpen n hS hl] at hh
  have hShift : iteratedFDeriv ℝ n H (l y) = iteratedFDeriv ℝ n f (lam, y) := by
    simpa [H, l, g, b] using iteratedFDeriv_comp_add_right (𝕜 := ℝ) (f := f) n b (l y)
  rw [hShift] at hh
  have heq : iteratedFDeriv ℝ n (fun z => f (lam, z)) y =
      (iteratedFDeriv ℝ n f (lam, y)).compContinuousLinearMap (fun _ => l) := by
    simpa [H, Function.comp_def, l, g, b] using hh
  rw [heq]
  exact ContinuousMultilinearMap.norm_compContinuous_linearIsometry_le _ (fun _ => g)

/-- A finite family of jointly smooth coefficients has uniform spatial jet
bounds on a fixed compact base for all sufficiently small dilations. -/
theorem exists_uniform_slice_jet_bound {J : Type*} [Fintype J] {K : Set (X dim)}
    (hK : IsCompact K) {U : Set (ℝ × (X dim))} (hU : IsOpen U)
    (hbase : ∀ y ∈ K, ((0 : ℝ), y) ∈ U) {B : J → ℝ × (X dim) → ℝ}
    (hB : ∀ j, ContDiffOn ℝ ∞ (B j) U) (N : ℕ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ᶠ lam in 𝓝 (0 : ℝ), ∀ y ∈ K, (lam, y) ∈ U ∧
      ∀ (j : J) (n : ℕ), n ≤ N →
        ‖iteratedFDeriv ℝ n (fun z => B j (lam, z)) y‖ ≤ C := by
  let F (q : J × Fin (N + 1)) (p : ℝ × (X dim)) := ‖iteratedFDeriv ℝ q.2.val (B q.1) p‖
  have hF (q : J × Fin (N + 1)) : ContinuousOn (F q) U := by
    intro p hp
    exact (((hB q.1).contDiffAt (hU.mem_nhds hp)).continuousAt_iteratedFDeriv
      (by simp : (q.2.val : ℕ∞ω) ≤ ∞)).norm.continuousWithinAt
  have hbound (q : J × Fin (N + 1)) : ∃ C : ℝ, 0 ≤ C ∧ ∀ y ∈ K, F q (0, y) ≤ C := by
    have hc : ContinuousOn (fun y => F q (0, y)) K :=
      (hF q).comp (continuous_const.prodMk continuous_id).continuousOn hbase
    obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hc
    exact ⟨max C 0, le_max_right _ _, fun y hy => (le_abs_self _).trans
      ((hC y hy).trans (le_max_left _ _))⟩
  choose D hD hDupper using hbound
  let C : ℝ := 1 + ∑ q, D q
  have hC : 1 ≤ C := le_add_of_nonneg_right (Finset.sum_nonneg fun q _ => hD q)
  refine ⟨C, hC, ?_⟩
  have hevery : ∀ᶠ lam in 𝓝 (0 : ℝ), ∀ y ∈ K, (lam, y) ∈ U ∧
      ∀ q, F q (lam, y) < C := by
    apply hK.eventually_forall_of_forall_eventually
    intro y hy
    have hU₀ := hU.mem_nhds (hbase y hy)
    have hCq (q : J × Fin (N + 1)) : F q (0, y) < C := by
      have hb := (hDupper q y hy).trans (Finset.single_le_sum
        (fun q _ => hD q) (Finset.mem_univ q))
      exact hb.trans_lt (lt_one_add _)
    have hn : ∀ᶠ p : ℝ × (X dim) in 𝓝 ((0 : ℝ), y), ∀ q, F q p < C :=
      Filter.eventually_all.mpr fun q =>
        ((hF q).continuousAt hU₀).preimage_mem_nhds (Iio_mem_nhds (hCq q))
    filter_upwards [hU₀, hn] with p hp hq
    exact ⟨hp, hq⟩
  filter_upwards [hevery] with lam hlam y hy
  obtain ⟨hUy, hFy⟩ := hlam y hy
  refine ⟨hUy, fun j n hn => ?_⟩
  let q : J × Fin (N + 1) := (j, ⟨n, Nat.lt_succ_of_le hn⟩)
  exact (norm_iteratedFDeriv_slice_le hU (hB j) hUy n).trans (hFy q).le

end CalderonN
