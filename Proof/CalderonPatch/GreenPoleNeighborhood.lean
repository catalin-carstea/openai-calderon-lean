module

public import Proof.CalderonPatch.GreenInversePairing

import Proof.CalderonPatch.ChartDensity
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic

public section

noncomputable section
open Filter MeasureTheory Metric Set
open scoped ContDiff ENNReal Manifold Topology

namespace CalderonPatch

open CalderonN (X chartTest contMDiff_chartTest tsupport_chartTest_subset)

variable {m : ℕ} {M : Type*} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanHalfSpace (m+1)) M] [IsManifold (𝓡∂ (m+1)) ∞ M]
  [MeasurableSpace M] [BorelSpace M]

local notation "J" => 𝓡∂ (m+1)
local notation "R" => 𝓘(ℝ,ℝ)
local notation "Y" => X (m+1)
local notation "Source" => smoothSourceSubmodule (m := m) (M := M)

namespace GreenPole

/-- A labeled shrinking family of neighborhoods and their compatible
smooth cutoffs. All supports remain inside the interior. -/
structure Neighborhoods (p : M) where
  region : ℕ → Set M
  region_closed : ∀ n, IsClosed (region n)
  region_interior : ∀ n, region n ⊆ (J).interior M
  shrinking : ∀ U ∈ 𝓝 p, ∀ᶠ n : ℕ in atTop, region n ⊆ U
  cutoff : ℕ → Source
  cutoff_in_range : ∀ n x, cutoff n x ∈ Icc (0 : ℝ) 1
  cutoff_support : ∀ n, tsupport (cutoff n : M → ℝ) ⊆ region n
  cutoff_one_near : ∀ n, (cutoff n : M → ℝ) =ᶠ[𝓝 p] 1

/-- Interior charts provide explicit neighborhoods shrinking to a
single observation point and exact plateau cutoffs on them. -/
theorem exists_neighborhoods {p : M} (hp : p ∈ (J).interior M) :
    Nonempty (Neighborhoods (m := m) p) := by
  obtain ⟨e,hpS,_,heI,he,hes⟩ := exists_interiorChart p hp isOpen_univ (mem_univ p)
  obtain ⟨R₀,hR,hT⟩ := Metric.mem_nhds_iff.mp
    (e.open_target.mem_nhds (e.map_source hpS))
  let r (n : ℕ) : ℝ := R₀ * (1 / ((n : ℝ)+1)) / 2
  have hr (n : ℕ) : 0 < r n := by dsimp [r]; positivity
  have hrR (n : ℕ) : r n < R₀ := by
    have hN : 1 ≤ (n : ℝ)+1 := by linarith [Nat.cast_nonneg (α := ℝ) n]
    have he' : 1 / ((n : ℝ)+1) ≤ 1 := div_le_one (by positivity) |>.mpr hN
    have he := mul_le_mul_of_nonneg_left he' hR.le
    dsimp only [r]
    linarith
  have hrad : Tendsto r atTop (𝓝 0) := by
    have := ((tendsto_const_nhds (x := R₀)).mul
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))).div_const 2
    simpa [r] using this
  let B (n : ℕ) := closedBall (e p) (r n)
  have hBT (n : ℕ) : B n ⊆ e.target := (closedBall_subset_ball (hrR n)).trans hT
  let χ (n : ℕ) : ContDiffBump (e p) :=
    ⟨r n/2,r n,by positivity,by linarith [hr n]⟩
  have hs (n : ℕ) : tsupport (χ n : Y → ℝ) ⊆ e.target := by
    rw [(χ n).tsupport_eq]
    exact hBT n
  have hsc (n : ℕ) := tsupport_chartTest_subset e (χ n).hasCompactSupport (hs n)
  let W (n : ℕ) := e.symm '' B n
  let φ (n : ℕ) : Source :=
    ⟨chartTest e (χ n),contMDiff_chartTest e he (χ n).contDiff (χ n).hasCompactSupport (hs n)⟩
  refine ⟨⟨W, ?_,?_,?_,φ,?_,?_,?_⟩⟩
  · intro n
    exact ((isCompact_closedBall _ _).image_of_continuousOn
      (e.continuousOn_symm.mono (hBT n))).isClosed
  · intro n x hx
    obtain ⟨z,hz,rfl⟩ := hx
    exact heI (e.map_target (hBT n hz))
  · intro U hU
    have hpre : e.symm ⁻¹' U ∈ 𝓝 (e p) := by
      have hC := e.continuousOn_symm.continuousAt (e.open_target.mem_nhds (e.map_source hpS))
      exact hC.preimage_mem_nhds (by rwa [e.left_inv hpS])
    obtain ⟨s,hs,hB⟩ := Metric.mem_nhds_iff.mp hpre
    filter_upwards [hrad.eventually (eventually_lt_nhds hs)] with n hn
    rintro x ⟨z,hz,rfl⟩
    exact hB (closedBall_subset_ball hn hz)
  · intro n x
    by_cases hx : x ∈ e.source
    · change chartTest e (χ n) x ∈ Icc (0 : ℝ) 1
      rw [chartTest,indicator_of_mem hx,Function.comp_apply]
      exact ⟨(χ n).nonneg,(χ n).le_one⟩
    · change chartTest e (χ n) x ∈ Icc (0 : ℝ) 1
      rw [chartTest,indicator_of_notMem hx]
      exact ⟨le_rfl,zero_le_one⟩
  · intro n
    change tsupport (chartTest e (χ n)) ⊆ W n
    refine (hsc n).trans ?_
    rw [(χ n).tsupport_eq]
  · intro n
    have hP := e.continuousOn.continuousAt (e.open_source.mem_nhds hpS)
    have hBall := hP.preimage_mem_nhds (ball_mem_nhds (e p) (χ n).rIn_pos)
    filter_upwards [hBall,e.open_source.mem_nhds hpS] with x hx hxS
    change chartTest e (χ n) x = 1
    rw [chartTest,indicator_of_mem hxS,Function.comp_apply]
    exact (χ n).one_of_mem_closedBall (ball_subset_closedBall hx)

omit [IsManifold (𝓡∂ (m+1)) ∞ M] [MeasurableSpace M] [BorelSpace M] in
/-- Shrinking neighborhoods eventually omit any different point. -/
theorem Neighborhoods.eventually_off {p : M} (N : Neighborhoods (m := m) p)
    {x : M} (hx : x ≠ p) :
    ∀ᶠ n : ℕ in atTop, x ∉ N.region n :=
  (N.shrinking ({x} : Set M)ᶜ (isClosed_singleton.isOpen_compl.mem_nhds
    (notMem_singleton_iff.mpr hx.symm))).mono fun _ hn h => hn h (mem_singleton x)

end GreenPole

end CalderonPatch
