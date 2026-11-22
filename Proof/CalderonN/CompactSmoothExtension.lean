module

public import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
public import Mathlib.Analysis.Calculus.ContDiff.Operations

import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.Tactic

public section

noncomputable section
open Set Filter
open scoped ContDiff Topology

namespace CalderonN

variable {P F : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Cut off a smooth field outside a neighborhood of a compact set. The
extension agrees on an open neighborhood of the entire compact set. -/
theorem exists_contDiff_extension_near_compact
    {U K : Set P} (hU : IsOpen U) (hK : IsCompact K) (hKU : K ⊆ U)
    {f : P → F} (hf : ContDiffOn ℝ ∞ f U) :
    ∃ g : P → F, ContDiff ℝ ∞ g ∧ HasCompactSupport g ∧
      ∃ V : Set P, IsOpen V ∧ K ⊆ V ∧ V ⊆ U ∧ EqOn g f V := by
  obtain ⟨W,hW,hKW,hWU,hWK⟩ := exists_open_between_and_isCompact_closure hK hU hKU
  obtain ⟨V,hV,hKV,hVW,_⟩ := exists_open_between_and_isCompact_closure hK hW hKW
  obtain ⟨χ,hχ,_,hSupp,hOne⟩ :=
    exists_contDiff_support_eq_eq_one_iff (n := (⊤ : ℕ∞)) hW isClosed_closure hVW
  let g (x : P) := χ x • f x
  have hOff (x : P) (hx : x ∉ W) : g x = 0 := by
    have hχ₀ : χ x = 0 := by
      by_contra h
      apply hx
      rw [← hSupp]
      exact h
    simp only [g,hχ₀,zero_smul]
  refine ⟨g,contDiff_iff_contDiffAt.mpr (fun x => ?_),?_,V,hV,hKV,
    subset_closure.trans (hVW.trans (subset_closure.trans hWU)),?_⟩
  · by_cases hx : x ∈ U
    · exact hχ.contDiffAt.smul (hf.contDiffAt (hU.mem_nhds hx))
    · apply (contDiffAt_const (c := (0:F))).congr_of_eventuallyEq
      have hC : x ∉ closure W := fun hxW => hx (hWU hxW)
      filter_upwards [isClosed_closure.isOpen_compl.mem_nhds hC] with z hz
      exact hOff z (fun h => hz (subset_closure h))

  · apply hWK.of_isClosed_subset (isClosed_tsupport _)
    apply closure_minimal _ isClosed_closure
    intro x hx
    by_contra h
    exact hx (hOff x (fun hW => h (subset_closure hW)))
  · intro x hx
    have he := (hOne x).1 (subset_closure hx)
    show χ x • f x = _
    rw [he,one_smul]

end CalderonN
