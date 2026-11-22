module

public import Proof.CalderonN.WeakHarmonicSpace
public import Mathlib.Analysis.Calculus.ContDiff.Bounds

import Proof.CalderonN.EllipticCalculus
import Proof.CalderonN.ClassicalInteriorJets
import Mathlib.Tactic

public section

noncomputable section
open Set MeasureTheory
open scoped Topology ContDiff

namespace CalderonN

variable {d : ℕ}

/-- A local interior derivative estimate in the actual chart (L^2) norm,
quantified over classical representatives. -/
@[expose] def HarmonicInteriorJets (U : Set (X d)) (g : (MetricField d)) : Prop :=
  ∀ (K : Set (X d)), IsCompact K → K ⊆ U → ∀ k : ℕ,
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (u : ChartL2 (d := d) U) (f : (X d) → ℝ), Harmonic U g f →
      (u : (X d) → ℝ) =ᵐ[(volume : Measure (X d)).restrict U] f →
      ∀ x ∈ K, ‖iteratedFDeriv ℝ k f x‖ ≤ C * ‖u‖

/-- The derivative estimate for a fixed smooth metric. -/
theorem harmonicInteriorJets_of_smoothMetric [NeZero d] {U : Set (X d)} (hU : IsOpen U)
    {g : MetricField d} (hg : SmoothMetric U g) : HarmonicInteriorJets U g := by
  intro K hK hKU k
  obtain ⟨C,hC,h⟩ := exists_uniform_harmonic_interior_jet_bound
    (isCompact_singleton (x := (0:ℝ))) hU (g := fun _ => g) (fun _ _ => hg)
    (fun i j => (contDiffOn_divergenceCoeff hg i j).comp contDiff_snd.contDiffOn
      (fun _ hz => hz.2)) hK hKU k
  exact ⟨C,hC,h 0 (mem_singleton _)⟩

/-- Compactly supporting a harmonic representative gives a uniform
global bound on each derivative of the cutoff representative. -/
theorem exists_global_cutoff_jet_bound {U : Set (X d)} (hU : IsOpen U) {g : (MetricField d)}
    (hjet : HarmonicInteriorJets U g) {χ : (X d) → ℝ}
    (hχ : ContDiff ℝ ∞ χ) (hχc : HasCompactSupport χ) (hχU : tsupport χ ⊆ U)
    (k : ℕ) : ∃ C : ℝ, 0 ≤ C ∧ ∀ (u : ChartL2 (d := d) U) (f : (X d) → ℝ), Harmonic U g f →
      (u : (X d) → ℝ) =ᵐ[(volume : Measure (X d)).restrict U] f →
      ∀ x : (X d), ‖iteratedFDeriv ℝ k (fun y => χ y * f y) x‖ ≤ C * ‖u‖ := by
  choose B hB hbound using hjet (tsupport χ) hχc hχU
  have hcb (m : ℕ) : ∃ A : ℝ, 0 ≤ A ∧ ∀ x ∈ tsupport χ, ‖iteratedFDeriv ℝ m χ x‖ ≤ A := by
    obtain ⟨A,hA⟩ := hχc.exists_bound_of_continuousOn
      ((hχ.continuous_iteratedFDeriv (m := m) (by simp)).continuousOn)
    exact ⟨max A 0,le_max_right _ _,fun x hx => (hA x hx).trans (le_max_left _ _)⟩
  choose A hA hAbound using hcb
  let C := ∑ m ∈ Finset.range (k+1), (k.choose m : ℝ) * A m * B (k-m)
  have hC : 0 ≤ C := Finset.sum_nonneg fun m _ =>
    mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (hA m)) (hB (k-m))
  refine ⟨C, hC, fun u f hf hrep x => ?_⟩
  by_cases hx : x ∈ tsupport χ
  · have hxU := hχU hx
    have hmul := norm_iteratedFDerivWithin_mul_le hχ.contDiffOn hf.1 hU.uniqueDiffOn hxU
      (n := k) (by simp)
    simp_rw [iteratedFDerivWithin_of_isOpen _ hU hxU] at hmul
    refine hmul.trans ?_
    rw [show C = _ from rfl, Finset.sum_mul]
    apply Finset.sum_le_sum
    intro m _
    rw [mul_assoc ((k.choose m : ℝ) * A m)]
    exact mul_le_mul
      (mul_le_mul_of_nonneg_left (hAbound m x hx) (Nat.cast_nonneg _))
      (hbound (k-m) u f hf hrep x hx) (norm_nonneg _)
      (mul_nonneg (Nat.cast_nonneg _) (hA m))
  · have he : (fun y => χ y * f y) =ᶠ[𝓝 x] fun _ => (0 : ℝ) :=
      by
        filter_upwards [isClosed_tsupport χ |>.isOpen_compl.mem_nhds hx] with y hy
        rw [image_eq_zero_of_notMem_tsupport hy, zero_mul]
    rw [(he.iteratedFDeriv (𝕜 := ℝ) k).eq_of_nhds]
    have hz : iteratedFDeriv ℝ k (fun _ : (X d) => (0 : ℝ)) x = 0 := by
      cases k with
      | zero => ext z; simp
      | succ k => exact congrFun (iteratedFDeriv_const_of_ne (𝕜 := ℝ) (E := (X d)) (Nat.succ_ne_zero k) (0 : ℝ)) x
    rw [hz,norm_zero]
    exact mul_nonneg hC (norm_nonneg _)

end CalderonN
