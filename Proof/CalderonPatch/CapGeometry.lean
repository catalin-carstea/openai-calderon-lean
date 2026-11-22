module

public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Topology.Connected.Basic

import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Tactic.Linarith

@[expose] public section

noncomputable section
open Set
open scoped ContDiff

namespace CalderonPatch

variable {Z : Type*}

/-- The open added part between the original and moved boundaries. -/
def exteriorCap (b : Z → ℝ) : Set (Z × ℝ) :=
  {p | -b p.1 < p.2 ∧ p.2 < 0}

/-- The moved boundary is the graph of the negative bump. -/
def shiftedHalfSpace (b : Z → ℝ) : Set (Z × ℝ) :=
  {p | -b p.1 ≤ p.2}

theorem isOpen_exteriorCap [TopologicalSpace Z] {b : Z → ℝ} (hb : Continuous b) :
    IsOpen (exteriorCap b) :=
  (isOpen_lt ((hb.comp continuous_fst).neg) continuous_snd).inter
    (isOpen_lt continuous_snd continuous_const)

/-- The cap is the continuous image of the bump positivity set times
the open unit interval. No regularity of its narrowing edge is needed. -/
theorem isConnected_exteriorCap [TopologicalSpace Z] {b : Z → ℝ} (hb : Continuous b)
    (hP : IsConnected {x | 0 < b x}) : IsConnected (exteriorCap b) := by
  let P := {x | 0 < b x}
  let k : Z × ℝ → Z × ℝ := fun p => (p.1, -b p.1 * p.2)
  have hk : Continuous k := continuous_fst.prodMk ((hb.comp continuous_fst).neg.mul continuous_snd)
  have hK : IsConnected (P ×ˢ Ioo (0 : ℝ) 1) := hP.prod (isConnected_Ioo zero_lt_one)
  have hEq : k '' (P ×ˢ Ioo (0 : ℝ) 1) = exteriorCap b := by
    ext p
    constructor
    · rintro ⟨⟨z,t⟩, ⟨hz, ht⟩, rfl⟩
      have h : -b z < 0 := neg_lt_zero.mpr hz
      change -b z < -b z * t ∧ -b z * t < 0
      exact ⟨by simpa only [mul_one] using mul_lt_mul_of_neg_left ht.2 h,
        mul_neg_of_neg_of_pos h ht.1⟩
    · rintro ⟨hlo, hhi⟩
      have h : -b p.1 < 0 := hlo.trans hhi
      have hP : p.1 ∈ P := neg_lt_zero.mp h
      let t := p.2 / (-b p.1)
      have ht : t ∈ Ioo (0 : ℝ) 1 := by
        refine ⟨div_pos_of_neg_of_neg hhi h, ?_⟩
        exact (div_lt_iff_of_neg h).mpr (by simpa only [one_mul] using hlo)
      refine ⟨(p.1,t), ⟨hP, ht⟩, Prod.ext rfl ?_⟩
      change (-b p.1) * (p.2 / (-b p.1)) = p.2
      rw [mul_comm, div_mul_cancel₀ _ h.ne]
  rw [← hEq]
  exact hK.image k hk.continuousOn

/-- The graph is straightened by translation in the normal variable.
The two maps are global inverses, including at the flat edge of the bump. -/
theorem smooth_shiftedHalfSpace_coordinates [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    {b : Z → ℝ} (hb : ContDiff ℝ ∞ b) :
    ∃ F G : Z × ℝ → Z × ℝ, ContDiff ℝ ∞ F ∧ ContDiff ℝ ∞ G ∧
      Function.LeftInverse G F ∧ Function.RightInverse G F ∧
      F ⁻¹' (univ ×ˢ Ici (0 : ℝ)) = shiftedHalfSpace b := by
  let F : Z × ℝ → Z × ℝ := fun p => (p.1, p.2 + b p.1)
  let G : Z × ℝ → Z × ℝ := fun p => (p.1, p.2 - b p.1)
  have hb' := hb.comp (contDiff_fst : ContDiff ℝ ∞ (Prod.fst : Z × ℝ → Z))
  refine ⟨F, G, contDiff_fst.prodMk (contDiff_snd.add hb'),
    contDiff_fst.prodMk (contDiff_snd.sub hb'), ?_, ?_, ?_⟩
  · intro p
    exact Prod.ext rfl (add_sub_cancel_right p.2 (b p.1))
  · intro p
    exact Prod.ext rfl (sub_add_cancel p.2 (b p.1))
  · ext p
    change ((True ∧ 0 ≤ p.2 + b p.1) ↔ -b p.1 ≤ p.2)
    simp only [true_and]
    constructor <;> intro h <;> linarith

end CalderonPatch
