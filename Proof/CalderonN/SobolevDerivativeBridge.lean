module

public import Proof.CalderonN.Coordinates
public import Proof.ReleasedAnalysis.TauCeti.Analysis.Sobolev.Wkp.Classical
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

import Mathlib.Tactic

/-! Adapted from `Calderon/CollaboratorLocalSobolevRawTwoJetBoundOct17.lean`
at `d6704c49395a38eb07e0249afeb8ea83d67971cc`. The proof identifies the
classical derivatives with the released Sobolev jets. -/

public section

noncomputable section
open MeasureTheory Set Metric TopologicalSpace
open scoped ENNReal ContDiff

namespace CalderonN

variable {d : ℕ}


/-- A Sobolev function of order `m` has lower-order truncations of no larger norm with the same
value component. -/
theorem exists_lower (U : Opens (X d)) : ∀ (m : ℕ) (u : TauCeti.Wkp (volume : Measure (X d)) U 2 m)
    (k : ℕ), k ≤ m →
    ∃ v : TauCeti.Wkp (volume : Measure (X d)) U 2 k, ‖v‖ ≤ ‖u‖ ∧
      TauCeti.Wkp.value k v = TauCeti.Wkp.value m u
  | 0, u, k, hk => by
      obtain rfl : k = 0 := by omega
      exact ⟨u, le_rfl, rfl⟩
  | m + 1, u, k, hk => by
      rcases Nat.lt_or_ge k (m + 1) with h | h
      · obtain ⟨v, hv, hv'⟩ := exists_lower U m (TauCeti.Wkp.lowerOrder m u) k (by omega)
        refine ⟨v, hv.trans (TauCeti.Wkp.norm_lowerOrder_le m u), ?_⟩
        rw [hv', TauCeti.Wkp.value_succ]
      · obtain rfl : k = m + 1 := by omega
        exact ⟨u, le_rfl, rfl⟩

/-- Classical derivatives through the Sobolev order of a smooth representative are bounded in
`L²(U)` by the native graph norm. -/
theorem eLpNorm_iteratedFDeriv_le (U : Opens (X d)) (m : ℕ)
    (u : TauCeti.Wkp (volume : Measure (X d)) U 2 m)
    {f : (X d) → ℝ} (hf : ContDiffOn ℝ ∞ f U)
    (hu : (TauCeti.Wkp.value m u : (X d) → ℝ) =ᵐ[(volume : Measure (X d)).restrict U] f)
    (k : ℕ) (hk : k ≤ m) :
    eLpNorm (iteratedFDeriv ℝ k f) 2 ((volume : Measure (X d)).restrict U) ≤
      ENNReal.ofReal ‖u‖ := by
  obtain ⟨v, hv, hvu⟩ := exists_lower U m u k hk
  have hv' : (TauCeti.Wkp.value k v : (X d) → ℝ) =ᵐ[(volume : Measure (X d)).restrict U] f := by
    rw [hvu]; exact hu
  refine le_trans ?_ (ENNReal.ofReal_le_ofReal hv)
  cases k with
  | zero =>
    have h : eLpNorm (iteratedFDeriv ℝ 0 f) 2 ((volume : Measure (X d)).restrict U) =
        eLpNorm (TauCeti.Wkp.value 0 v : (X d) → ℝ) 2 ((volume : Measure (X d)).restrict U) := by
      refine eLpNorm_congr_norm_ae ?_ (Lp.aestronglyMeasurable _) ?_
      · exact (ContinuousOn.continuousOn_iteratedFDeriv hf U.isOpen
          (by exact_mod_cast le_top)).aestronglyMeasurable U.isOpen.measurableSet
      filter_upwards [hv'] with x hx
      rw [norm_iteratedFDeriv_zero, hx]
    rw [h, ← Lp.enorm_def, ← ofReal_norm]
    exact ENNReal.ofReal_le_ofReal (TauCeti.Wkp.norm_value_le 0 v)
  | succ j =>
    have hg := TauCeti.Wkp.iteratedGradient_ae_eq_of_contDiffOn j v
      (hf.of_le (by exact_mod_cast le_top)) hv'
    have h : eLpNorm (iteratedFDeriv ℝ (j + 1) f) 2 ((volume : Measure (X d)).restrict U) =
        eLpNorm (TauCeti.Wkp.iteratedGradient j v : (X d) → TauCeti.IteratedGradient (X d) j) 2
          ((volume : Measure (X d)).restrict U) := by
      refine eLpNorm_congr_norm_ae ?_ (Lp.aestronglyMeasurable _) ?_
      · exact (ContinuousOn.continuousOn_iteratedFDeriv hf U.isOpen
          (by exact_mod_cast le_top)).aestronglyMeasurable U.isOpen.measurableSet
      filter_upwards [hg] with x hx
      rw [hx, TauCeti.norm_iteratedGradientChain]
    rw [h, ← Lp.enorm_def, ← ofReal_norm]
    exact ENNReal.ofReal_le_ofReal (TauCeti.Wkp.norm_iteratedGradient_le j v)

end CalderonN
