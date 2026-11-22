module

public import Proof.CalderonN.CompactPointEvaluation
public import Proof.CalderonN.InteriorWordEnergy

import Mathlib.Tactic

public section

noncomputable section
open Set MeasureTheory
open scoped ContDiff Topology

namespace CalderonN.Elliptic

variable {d : ℕ} [NeZero d]


/-- A common pointwise derivative estimate on a compact set, for every
member of the specified compact coefficient family. -/
theorem exists_interior_word_point_bound_family
    {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    {J : Set P} (hJ : IsCompact J) {U K : Set (X d)}
    (hU : IsOpen U) (hK : IsCompact K) (hKU : K ⊆ U)
    (a : P → (I d) → (I d) → (X d) → ℝ) (ha : ∀ i j, Strict.JointSmooth (fun p => a p i j))
    (hpos : ∀ p ∈ J, ∀ x ∈ U, Matrix.PosDef (fun i j => a p i j x : (Mat d))) (w : List (I d)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ p ∈ J, ∀ (u : (X d) → ℝ), ContDiff ℝ ∞ u →
      (∀ x ∈ U, Lop (a p) u x = 0) → IntegrableOn (fun x => u x ^ 2) U →
      ∀ x ∈ K, |wordDeriv w u x| ≤ C * Real.sqrt (∫ y in U, u y^2) := by
  obtain ⟨χ,hχ,hχc,hχU,hχK⟩ := exists_plateau_cutoff hU hK hKU
  let L := tsupport χ
  let v := (fullCoordinateWord d) ++ w
  obtain ⟨A,hA,hbound⟩ := exists_interior_word_energy_bound_family hJ hU a ha hpos v.length hχc hχU
  obtain ⟨B,hB,hcut⟩ := exists_cutoff_word_energy_constant hχc hχ v
  let M := Real.sqrt ((volume : Measure (X d)).real L)
  refine ⟨M*Real.sqrt (B*A),by positivity,fun p hpJ u hu hpde hint x hx => ?_⟩
  let z (y : (X d)) := χ y*u y
  let f := wordDeriv w z
  have hz : ContDiff ℝ ∞ z := hχ.mul hu
  have hL : tsupport z ⊆ L := tsupport_mul_subset_left
  have hfL := (tsupport_wordDeriv_subset w z).trans hL
  have hp := abs_apply_le_volume_sqrt_word (contDiff_wordDeriv w hz) hχc hfL x
  have hzEq : z =ᶠ[𝓝 x] u := (hχK x hx).mono (fun y hy => by simp [z,hy])
  have hfEq := (wordDeriv_congr_germ w hzEq).eq_of_nhds
  rw [hfEq] at hp
  have hJ := hcut u (A*(∫ y in U, u y^2)) hu (hbound p hpJ u hu hpde hint)
  rw [show v = fullCoordinateWord d ++ w from rfl, wordDeriv_append] at hJ
  change (∫ y in L, wordDeriv (fullCoordinateWord d) f y^2) ≤ _ at hJ
  calc
    _ ≤ _ := hp
    _ ≤ M * Real.sqrt (B * (A*(∫ y in U, u y^2))) :=
      mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hJ) (Real.sqrt_nonneg _)
    _ = _ := by rw [← mul_assoc B A,Real.sqrt_mul (mul_nonneg hB hA)]; ring

/-- Pointwise estimates for a fixed divergence-form equation. -/
theorem exists_interior_word_point_bound {U K : Set (X d)}
    (hU : IsOpen U) (hK : IsCompact K) (hKU : K ⊆ U)
    (a : (I d) → (I d) → (X d) → ℝ) (ha : ∀ i j, ContDiff ℝ ∞ (a i j))
    (hpos : ∀ x ∈ U, Matrix.PosDef (fun i j => a i j x : (Mat d))) (w : List (I d)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (u : (X d) → ℝ), ContDiff ℝ ∞ u →
      (∀ x ∈ U, Lop a u x = 0) → IntegrableOn (fun x => u x ^ 2) U →
      ∀ x ∈ K, |wordDeriv w u x| ≤ C * Real.sqrt (∫ y in U, u y^2) := by
  obtain ⟨C,hC,h⟩ := exists_interior_word_point_bound_family (isCompact_singleton (x := (0:ℝ))) hU hK hKU
    (fun _ => a) (fun i j => (ha i j).comp contDiff_snd) (fun _ _ x hx => hpos x hx) w
  exact ⟨C,hC,h 0 (mem_singleton _)⟩

end CalderonN.Elliptic
