module

public import Proof.CalderonN.CylinderCutoff
public import Proof.CalderonN.Radius

import Proof.CalderonN.DilationGeometry
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Tactic

@[expose] public section

open Set Filter Metric
open scoped ContDiff Topology

namespace CalderonN

variable {dim : ℕ} {normal : I dim}
open FixedTube

theorem exists_cylinderDepth_lipschitz (L : ℝ) :
    ∃ l, LipschitzOnWith l (conformalDepth normal L) (interior (coordinateCylinder normal)) := by
  obtain ⟨l, hl⟩ := ((contDiff_conformalDepth (normal := normal)) L).contDiffOn.exists_lipschitzOnWith (by simp)
    (convex_closedBall (0 : (X dim)) 2) (isCompact_closedBall (0 : (X dim)) 2)
  exact ⟨l, hl.mono (interior_subset.trans (coordinateCylinder_subset_closedBall (normal := normal)))⟩

/-- The same dilation range covers the lower strip for both the cutoff
derivative and the complement of the compact bootstrap region. -/
theorem eventually_cylinderSeed_dichotomy
    {V W : Set (X dim)} (hV : IsOpen V) (h₀ : (0 : (X dim)) ∈ V)
    {s : (X dim) → ℝ} (hs : DifferentiableAt ℝ s 0) (hs₀ : s 0 = 0)
    (hside : {x ∈ V | s x < 0} ⊆ W) (hnormal : ∀ y, fderiv ℝ s 0 y = y normal)
    {L tb : ℝ} (htb : 0 < tb)
    (hm : ∀ y, conformalDepth normal L y ≤ 3 * tb → parabolicHeight normal y < 1 / 4) :
    ∀ᶠ lam in 𝓝 (0 : ℝ), 0 < lam →
      (∀ y ∈ interior (coordinateCylinder normal) \ cylinderCore normal L tb,
        lam • y ∈ W ∨ tb ≤ conformalDepth normal L y) ∧
      ∀ y ∈ tsupport (fderiv ℝ (cylinderCutoff normal L tb)),
        lam • y ∈ W ∨ tb ≤ conformalDepth normal L y := by
  let K : Set (X dim) := (coordinateCylinder normal) ∩ {y | y normal ≤ -(1/4 : ℝ)}
  have hK : IsCompact K :=
    (isCompact_coordinateCylinder (normal := normal)).inter_right
      (isClosed_le ((EuclideanSpace.proj normal : (X dim) →L[ℝ] ℝ).continuous) continuous_const)
  have hneg (y : (X dim)) (hy : y ∈ K) : fderiv ℝ s 0 y < 0 := by
    rw [hnormal]
    exact (show y normal ≤ -(1/4 : ℝ) from hy.2).trans_lt (by norm_num)
  have hlower := eventually_nhdsWithin_iff.mp
    (eventually_dilated_subset_of_negative_tangent hV h₀ hK hs hs₀ hside hneg)
  filter_upwards [hlower] with lam hlam hpos
  constructor
  · intro y hy
    by_cases h : -(1/2 : ℝ) ≤ y normal
    · right
      by_contra! hdep
      exact hy.2 ⟨interior_subset hy.1, h, by linarith⟩
    · left
      exact hlam hpos y ⟨interior_subset hy.1,
        (lt_of_not_ge h).le.trans (show -(1/2 : ℝ) ≤ -(1/4) by norm_num)⟩
  · intro y hy
    obtain hlo | hhi := (cylinderCutoff_differential_tsupport (normal := normal)) htb hy
    · left
      have hY := (cylinderCutoff_tsupport_subset_interior (normal := normal)) htb hm (tsupport_fderiv_subset ℝ hy)
      exact hlam hpos y ⟨interior_subset hY, (show y normal < -(1/4 : ℝ) from hlo).le⟩
    · exact Or.inr (show tb < conformalDepth normal L y from hhi).le

theorem shrinkingRadius_ge_of_cylinderDepth {L tb R δ : ℝ} (htb : 0 < tb)
    (hR : 0 ≤ R) (hδ : 0 < δ) (p : ℕ) {y : (X dim)} (hy : tb ≤ conformalDepth normal L y) :
    R * tb ^ p ≤ shrinkingRadius R p (conformalDepth normal L) δ y :=
  mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ htb.le (hy.trans ((le_max_left _ _).trans
      (sub_nonneg.mp (softplus_sub_max_bounds hδ (conformalDepth normal L y)).1))) p) hR

end CalderonN
