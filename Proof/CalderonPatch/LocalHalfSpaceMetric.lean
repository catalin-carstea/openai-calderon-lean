module

public import Proof.CalderonPatch.CapMetricExtension
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs

import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Tactic.Linarith

public section

noncomputable section
open Filter Matrix Metric Set
open scoped ContDiff Topology

namespace CalderonPatch

open CalderonN (I Mat lowerHalfSpace)

variable {n : ℕ} {Z : Type} [NormedAddCommGroup Z] [NormedSpace ℝ Z] [FiniteDimensional ℝ Z]

/-- A metric smooth on the original side of an open boundary chart
extends smoothly and positively to an open neighborhood of the seam.
The cutoff makes all its normal seam jets compactly supported before
applying the checked half-space extension. -/
theorem exists_local_halfSpace_metric_extension {U : Set (Z × ℝ)} (hU : IsOpen U)
    {a : Z} (ha : (a, (0 : ℝ)) ∈ U) {g : Z × ℝ → Mat n}
    (hg : ∀ i j, ContDiffOn ℝ ∞ (fun p => g p i j) (U ∩ lowerHalfSpace Z))
    (hPos : ∀ p ∈ U ∩ lowerHalfSpace Z, (g p).PosDef) :
    ∃ (V : Set (Z × ℝ)) (G : Z × ℝ → Mat n), IsOpen V ∧ (a, (0 : ℝ)) ∈ V ∧ V ⊆ U ∧
      (∀ i j, ContDiff ℝ ∞ (fun p => G p i j)) ∧
      (∀ p ∈ V, (G p).PosDef) ∧ EqOn G g (V ∩ lowerHalfSpace Z) := by
  classical
  let S := lowerHalfSpace Z
  let p : Z × ℝ := (a, 0)
  obtain ⟨r, hr, hrU⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds ha)
  let χ : ContDiffBump p := ⟨r / 4, r / 2, by positivity, by linarith⟩
  have hχU : tsupport (χ : Z × ℝ → ℝ) ⊆ U := by
    rw [χ.tsupport_eq]
    exact (closedBall_subset_ball (by change r / 2 < r; linarith)).trans hrU
  let f : Z × ℝ → Mat n := fun x => χ x • g x
  have hZero {x : Z × ℝ} (hx : x ∉ tsupport (χ : Z × ℝ → ℝ)) (i j : I n) :
      (fun y => f y i j) =ᶠ[𝓝 x] fun _ => 0 := by
    have h := notMem_tsupport_iff_eventuallyEq.mp hx
    filter_upwards [h] with y hy
    change χ y = 0 at hy
    simp [f, hy]
  have hF (i j : I n) : ContDiffOn ℝ ∞ (fun x => f x i j) S := by
    intro x hx
    by_cases hxU : x ∈ U
    · have h : ContDiffWithinAt ℝ ∞ (fun x => f x i j) (U ∩ S) x := by
        exact (χ.contDiffAt.contDiffWithinAt).mul (hg i j x ⟨hxU, hx⟩)
      have he : U ∩ S =ᶠ[𝓝 x] S := by
        filter_upwards [hU.mem_nhds hxU] with y hy
        simp [hy]
      exact (contDiffWithinAt_congr_set he).mp h
    · exact (contDiffAt_const.congr_of_eventuallyEq (hZero (fun h => hxU (hχU h)) i j)).contDiffWithinAt
  have hSym (x : Z × ℝ) (hx : x ∈ S) : (f x).transpose = f x := by
    by_cases h : x ∈ U
    · change (χ x • g x).transpose = χ x • g x
      rw [Matrix.transpose_smul, (hPos x ⟨h,hx⟩).isHermitian.isSymm.eq]
    · have hχ : χ x = 0 := image_eq_zero_of_notMem_tsupport (fun hS => h (hχU hS))
      simp [f, hχ]
  have hSupport (i j : I n) (k : ℕ) : HasCompactSupport (fun z : Z =>
      iteratedFDerivWithin ℝ k (fun x => f x i j) S (z,0) (fun _ => (0,1))) := by
    let A := Prod.fst '' tsupport (χ : Z × ℝ → ℝ)
    have hA : IsCompact A := χ.hasCompactSupport.image continuous_fst
    apply HasCompactSupport.intro hA
    intro z hz
    have hz0 : (z, (0 : ℝ)) ∉ tsupport (χ : Z × ℝ → ℝ) := fun h => hz (mem_image_of_mem Prod.fst h)
    have h := hZero hz0 i j
    rw [(h.filter_mono nhdsWithin_le_nhds).iteratedFDerivWithin_eq h.eq_of_nhds k,
      iteratedFDerivWithin_fun_zero]
    rfl
  obtain ⟨G, hG, hGSym, hEq⟩ := exists_symmetric_extension_lowerHalfSpace hF hSym hSupport
  have hAgree {x : Z × ℝ} (hx : x ∈ S) (hxr : dist x p ≤ r / 4) : G x = g x := by
    rw [hEq hx, show f x = χ x • g x from rfl, χ.one_of_mem_closedBall (mem_closedBall.mpr hxr), one_smul]
  let L := closedBall a (r / 8)
  have hL : IsCompact L := isCompact_closedBall _ _
  have hLPos (z : Z) (hz : z ∈ L) : (G (z, 0)).PosDef := by
    have hS : (z,(0 : ℝ)) ∈ S := ⟨mem_univ _, le_rfl⟩
    have hd : dist (z,(0 : ℝ)) p ≤ r / 8 := by simpa only [p, Prod.dist_eq, dist_self, max_eq_left dist_nonneg] using mem_closedBall.mp hz
    rw [hAgree hS (hd.trans (by linarith))]
    exact hPos _ ⟨hrU (mem_ball.mpr (hd.trans_lt (by linarith))), hS⟩
  obtain ⟨δ, hδ, hδPos⟩ := posDef_near_compact_slice hL hGSym (fun i j => (hG i j).continuous) hLPos
  let ρ := min (r / 8) δ
  let V := ball p ρ
  have hρ : 0 < ρ := lt_min (by positivity) hδ
  refine ⟨V, G, isOpen_ball, mem_ball_self hρ, ?_, hG, ?_, ?_⟩
  · exact (ball_subset_ball (by dsimp [ρ]; linarith [min_le_left (r / 8) δ])).trans hrU
  · rintro ⟨z,t⟩ hz
    have h := mem_ball.mp hz
    rw [show dist (z,t) p = max (dist z a) (dist t 0) from Prod.dist_eq, max_lt_iff] at h
    exact hδPos z (mem_closedBall.mpr (h.1.le.trans (min_le_left _ _))) t
      (mem_ball.mpr (h.2.trans_le (min_le_right _ _)))
  · intro x hx
    exact hAgree hx.2 ((mem_ball.mp hx.1).le.trans (by dsimp [ρ]; linarith [min_le_left (r / 8) δ]))

end CalderonPatch
