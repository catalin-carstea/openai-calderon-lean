module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Topology.Connected.Clopen
public import Mathlib.Topology.Maps.Proper.Basic

import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Tactic.Linarith

public section

open Set Filter
open scoped Topology

namespace CalderonN

/-- On a compact base, strict improvement and connectedness propagate the bound.
The compact projection argument follows the earlier Calderón formalization's
`forall_le_of_compact_half_improvement`. -/
theorem bound_of_strict_improvement
    {T E : Type*} [TopologicalSpace T] [PreconnectedSpace T]
    [TopologicalSpace E] [CompactSpace E]
    {H : E → ℝ} {b : T → E → ℝ}
    (hH : Continuous H) (hb : Continuous (Function.uncurry b))
    {t₀ : T} (hstart : ∀ y, H y ≤ b t₀ y)
    (himprove : ∀ t, (∀ y, H y ≤ b t y) → ∀ y, H y < b t y) :
    ∀ t y, H y ≤ b t y := by
  let good : Set T := {t | ∀ y, H y ≤ b t y}
  have hclosed : IsClosed good := by
    change IsClosed {t | ∀ y, H y ≤ b t y}
    rw [ofPred_forall]
    exact isClosed_iInter fun y =>
      isClosed_le continuous_const (hb.comp (continuous_id.prodMk continuous_const))
  let bad : Set (T × E) := {q | b q.1 q.2 ≤ H q.2}
  have hbad : IsClosed bad := isClosed_le hb (hH.comp continuous_snd)
  have heq : good = (Prod.fst '' bad)ᶜ := by
    ext t
    simpa [good, bad] using
      (show (∀ y, H y ≤ b t y) ↔ ∀ y, H y < b t y from
        ⟨himprove t, fun h y => (h y).le⟩)
  have hopen : IsOpen good := heq ▸ (isClosedMap_fst_of_compactSpace bad hbad).isOpen_compl
  have hall : good = univ := IsClopen.eq_univ ⟨hclosed, hopen⟩ ⟨t₀, hstart⟩
  intro t
  exact show t ∈ good from hall ▸ mem_univ t

/-- The radius hypothesis is checked on a single compact base at each
parameter. The factor-one-half gain uses the same radius and metric jets. -/
theorem shrinking_bounds
    {E : Type*} [TopologicalSpace E] {K : Set E} (hK : IsCompact K)
    {H : E → ℝ} {r : ℝ → E → ℝ} {ε : ℝ} (hε : 0 < ε)
    (hH : ContinuousOn H K)
    (hr : ContinuousOn (Function.uncurry r) (Ioc (0 : ℝ) 1 ×ˢ K))
    (hrpos : ∀ δ ∈ Ioc (0 : ℝ) 1, ∀ y ∈ K, 0 < r δ y)
    (hstart : ∀ y ∈ K, H y ≤ ε * r 1 y)
    (himprove : ∀ δ ∈ Ioc (0 : ℝ) 1, (∀ y ∈ K, H y ≤ ε * r δ y) →
      ∀ y ∈ K, H y ≤ (ε / 2) * r δ y) :
    ∀ δ ∈ Ioc (0 : ℝ) 1, ∀ y ∈ K, H y ≤ ε * r δ y := by
  let T := ↥(Ioc (0 : ℝ) 1)
  let : PreconnectedSpace T := isPreconnected_iff_preconnectedSpace.mp isPreconnected_Ioc
  let : CompactSpace K := isCompact_iff_compactSpace.mp hK
  let b (t : T) (y : K) := ε * r t y
  have hb : Continuous (Function.uncurry b) := by
    apply continuous_const.mul
    exact hr.comp_continuous
      ((continuous_subtype_val.comp continuous_fst).prodMk
        (continuous_subtype_val.comp continuous_snd))
      (fun q => ⟨q.1.property, q.2.property⟩)
  let one : T := ⟨1, by norm_num⟩
  have h := bound_of_strict_improvement
    (continuousOn_iff_continuous_domRestrict.mp hH) hb
    (t₀ := one) (fun y => hstart y y.property) (by
      intro t ht y
      exact (himprove t t.property (fun z hz => ht ⟨z, hz⟩) y y.property).trans_lt
        (mul_lt_mul_of_pos_right (by linarith) (hrpos t t.property y y.property)))
  exact fun δ hδ y hy => h ⟨δ, hδ⟩ ⟨y, hy⟩

/-- The pointwise shrinking limit is taken for one fixed field of metric jets. -/
theorem eq_zero_of_shrinking_bound {H ε : ℝ} (hH : 0 ≤ H) {r : ℝ → ℝ}
    (hr : Tendsto r (𝓝[Ioc (0 : ℝ) 1] 0) (𝓝 0))
    (hbound : ∀ δ ∈ Ioc (0 : ℝ) 1, H ≤ ε * r δ) :
    H = 0 := by
  let : (𝓝[Ioc (0 : ℝ) 1] 0).NeBot :=
    mem_closure_iff_nhdsWithin_neBot.mp (by simp [closure_Ioc] : 0 ∈ closure (Ioc (0 : ℝ) 1))
  have hlimit : Tendsto (fun δ => ε * r δ) (𝓝[Ioc (0 : ℝ) 1] 0) (𝓝 0) := by
    simpa only [mul_zero] using hr.const_mul ε
  exact le_antisymm (ge_of_tendsto hlimit (eventually_mem_nhdsWithin.mono hbound)) hH

/-- The interpolation order and radius exponent used in Section 6. The
    half-dimension term comes from rescaling the L² norm on a ball. -/
theorem interpolation_powers_le_three_halves {r : ℝ} (hr : 0 < r) (hr₁ : r ≤ 1)
    {n j m : ℕ} (hj : j ≤ 10) (hm : 10 + 3 * (10 + (n : ℝ) / 2) ≤ m) :
    r ^ ((2 : ℝ) - ((j : ℝ) + (n : ℝ) / 2) / (2 * (10 + (n : ℝ) / 2))) ≤ r ^ (3 / 2 : ℝ) ∧
    r ^ (((m : ℝ) - (j : ℝ)) / (2 * (10 + (n : ℝ) / 2))) ≤ r ^ (3 / 2 : ℝ) := by
  have hj' : (j : ℝ) ≤ 10 := by exact_mod_cast hj
  have hden : 0 < 2 * (10 + (n : ℝ) / 2) := by positivity
  constructor
  · apply Real.rpow_le_rpow_of_exponent_ge hr hr₁
    have h : ((j : ℝ) + (n : ℝ) / 2) / (2 * (10 + (n : ℝ) / 2)) ≤ 1 / 2 := by
      apply (div_le_iff₀ hden).mpr
      linarith
    linarith
  · apply Real.rpow_le_rpow_of_exponent_ge hr hr₁
    apply (le_div_iff₀ hden).mpr
    linarith

end CalderonN
